/* SPDX-License-Identifier: MIT */
/* {{{ Includes */

// This is emacs folding-mode

#include <assert.h>
#include <errno.h>
#include <limits.h>
#include <stdarg.h>
#include <stdalign.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

#define CAML_NAME_SPACE
#define CAML_INTERNALS

#include "boxroot.h"
#include <caml/minor_gc.h>
#include <caml/major_gc.h>

#if defined(_POSIX_TIMERS) && defined(_POSIX_MONOTONIC_CLOCK)
#define POSIX_CLOCK
#include <time.h>
#endif

#include "ocaml_hooks.h"
#include "platform.h"

#if OCAML_MULTICORE
#include <caml/lf_skiplist.h>
#endif

static_assert(!BXR_FORCE_REMOTE || BXR_MULTITHREAD,
              "invalid configuration");

/* }}} */

/* {{{ Data types */

enum {
  YOUNG = BXR_CLASS_YOUNG,
  OLD,
  UNTRACKED
};

struct bxr_private {
  bxr_slot contents;
};

typedef struct {
  /* index of a slot in the pool */
  halfptr_t a_next;
  /* length of the free list */
  halfptr_t a_dealloc_count;
} delayed_free_list;

static_assert(sizeof(delayed_free_list) == sizeof(void *),
              "Wrong _Atomic(delayed_free_list) size");

typedef struct pool {
  /* Each cell in `roots` has an owner who can access the cell.
     Unallocated cells are owned by the pool (thus by its domain). Who
     owns a boxroot owns its cell.

     In addition, the OCaml GC can access the cells concurrently. The
     OCaml GC assumes temporary ownership during stop-the-world
     sections, and while holding the mutex below.

     Consequently, access to the contents of `roots` is permitted for
     someone owning a cell either:
     - by holding _any_ domain lock, or
     - by holding the mutex below.

     The ownership discipline ensures that there are no concurrent
     mutations of the same cell coming from the mutator.

     To sum up, cells are protected by a combination of:
     - the user's ownership discipline,
     - the domain lock,
     - the pool mutex.

     Given that in order to dereference and modify a boxroot one needs
     a domain lock, the mutex is only needed by the mutator for the
     accesses during deallocations without holding any domain lock. */

  /* Free list, protected by domain lock. */
  bxr_free_list free_list;
  /* Owned by the pool ring. */
  struct pool *prev;
  struct pool *next;
  /* Note: `mutex` and `delayed_fl` are placed on their own cache
     line. Notably, together they fit on a cache line on Linux 64-bit
     and this only wastes two padding words. */
  /* Delayed free list. An MPSC stack which is lockfree when holding a
     domain. It requires the pool mutex when no domain lock is held in
     order to protect from scanning. */
  alignas(Cache_line_size) _Atomic(delayed_free_list) delayed_fl;
  /* The pool mutex */
  mutex_t mutex;
  /* Allocated slots hold OCaml values. Unallocated slots hold a
     pointer to the next slot in the free list, or to the pool itself,
     denoting the empty free list. */
  bxr_slot roots[];
} pool;

#define POOL_CAPACITY ((int)((BXR_POOL_SIZE - sizeof(pool)) / sizeof(bxr_slot)))

static_assert(BXR_POOL_SIZE / sizeof(bxr_slot) <= INT_MAX, "pool size too large");
static_assert(POOL_CAPACITY >= 1, "pool size too small");
static_assert(offsetof(pool, free_list) == 0, "incorrect free_list offset");

/* }}} */

/* {{{ Globals */

/* Trap for TLS initialization */
static bxr_free_list const empty_fl = { (bxr_slot_ref)&empty_fl, -1, -1, UNTRACKED };
/* empty_fl is never modified through this pointer */
static bxr_free_list * const empty_fl_ptr = (bxr_free_list *) &empty_fl;

/* Global pool rings and shared pointer to current free-list. */
typedef struct {
  /* Pool of old values: contains only roots pointing to the major
     heap. Scanned at the start of major collection. */
  pool *old;
  /* Pool of young values: contains roots pointing to the major or to
     the minor heap. Scanned at the start of minor and major
     collection. */
  pool *young;
  /* Current pool. Scanned at the start of minor and major collection.
     This ring is special: it has 0 or 1 pools, and its pool when it
     exists has an incorrect allocation count. See
     {set,take}_current_pool. */
  pool *current;
  /* Pointer to the current free list. Either equal to [&current->free_list], or
     to empty_fl_ptr. Only used if OCAML_MULTICORE.  */
  bxr_free_list *current_fl;
  /* Pools containing no root: not scanned.
     We could free these pools immediately, but this could lead to
     stuttering behavior for workloads that regularly come back to
     0 boxroots alive. Instead we wait for the next major root
     scanning to free empty pools. */
  pool *free;
  /* Whether the old pools have been reordered once since last minor
     to take delayed deallocations into account */
  bool reordered_since_minor;
} bxr_domain_state;

static void init_pool_rings(bxr_domain_state *dom_st)
{
  dom_st->old = NULL;
  dom_st->young = NULL;
  dom_st->current = NULL;
  dom_st->current_fl = empty_fl_ptr;
  dom_st->free = NULL;
  dom_st->reordered_since_minor = true;
}

static void free_pool_rings(bxr_domain_state *);

#if OCAML_MULTICORE

/* keys: int (domain + 1) --- 0 is reserved for internal use by lf_skiplist.h
   values: bxr_domain_state* (owned by its domain) */
static struct lf_skiplist domain_state_skiplist;

/* empty_fl_ptr is never modified through this pointer */
#define Cached_fl_ptr_init ((bxr_free_list **) &empty_fl_ptr)

/* We make DLS efficient by caching into implicit TLS */
/* Equal to NULL or to domain_state_skiplist[dom_id+1] after initialization */
_Thread_local bxr_domain_state *bxr_cached_domain_state = NULL;
/* Equal to Cached_fl_ptr_init, or to
   &domain_state_skiplist[dom_id+1]->current_fl after
   initialization. */
_Thread_local bxr_free_list **bxr_cached_fl_ptr = Cached_fl_ptr_init;

static void init_bxr_domain_state(void)
{
  caml_lf_skiplist_init(&domain_state_skiplist);
}

/* ownership required: domain (maybe uninit).

   The domain is uninitialized if get_bxr_domain_state returns NULL.
   There are three entry points into boxroot that must guard against
   this: bxr_create_slow, scanning_callback and
   domain_termination_callback. */
static bxr_domain_state *get_bxr_domain_state(int dom_id)
{
  if (bxr_cached_domain_state != NULL) return bxr_cached_domain_state;
  DEBUGassert(dom_id >= 0);
  uintnat key = dom_id + 1;
  bxr_domain_state *value = NULL;
  if (caml_lf_skiplist_find(&domain_state_skiplist, key, (uintnat *) &value)) {
    bxr_cached_domain_state = value;
  }
  return value;
}

/* ownership required: domain */
static void set_current_fl(bxr_domain_state *local, bxr_free_list *fl)
{
  DEBUGassert(local != NULL);
  local->current_fl = fl;
}

static bool thread_initialised(void)
{
  return bxr_cached_fl_ptr != Cached_fl_ptr_init;
}

/* ownership required: domain (maybe uninit) */
static bool init_thread(int dom_id)
{
  DEBUGassert(dom_id >= 0);
  bxr_domain_state *local = get_bxr_domain_state(dom_id);
  if (local == NULL) {
    local = malloc(sizeof(bxr_domain_state));
    if (local == NULL) return false;
    init_pool_rings(local);
    caml_lf_skiplist_insert(&domain_state_skiplist, dom_id + 1, (uintnat) local);
  }
  bxr_cached_fl_ptr = &local->current_fl;
  return true;
}

/* Assumes no thread succeeds the domain lock check anymore. */
static void free_domain_state()
{
  FOREACH_LF_SKIPLIST_ELEMENT(var, &domain_state_skiplist, {
      bxr_domain_state *dom_st = (bxr_domain_state *)var->data;
      free_pool_rings(dom_st);
      free(dom_st);
      caml_lf_skiplist_remove(&domain_state_skiplist, var->key);
    });
  caml_lf_skiplist_free_garbage(&domain_state_skiplist);
}


#else

/* ownership: runtime lock */
bxr_free_list *bxr_current_fl = empty_fl_ptr;

/* ownership: runtime lock */
static bxr_domain_state bxr_state = { NULL, };

static void init_bxr_domain_state(void) {};

/* ownership: runtime lock */
static bxr_domain_state *get_bxr_domain_state(int dom_id)
{
  DEBUGassert(dom_id == 0);
  return &bxr_state;
}

/* ownership required: domain */
static void set_current_fl(bxr_domain_state *, bxr_free_list *fl)
{
  bxr_current_fl = fl;
}

static bool thread_initialised(void) { return true; }
static bool init_thread(int) { return true; }

static void free_domain_state()
{
  free_pool_rings(&bxr_state);
  bxr_current_fl = empty_fl_ptr;
}

#endif

/* Holds the live pools of terminated domains until the next GC.
   Owned by orphan_mutex. */
static bxr_domain_state orphan = { NULL, };
static mutex_t orphan_mutex = BXR_MUTEX_INITIALIZER;

static struct {
  atomic_llong minor_collections;
  atomic_llong major_collections;
  atomic_llong total_create_young;
  atomic_llong total_create_old;
  atomic_llong total_create_slow;
  atomic_llong total_create_slow_time;
  atomic_llong total_delete_young;
  atomic_llong total_delete_old;
  atomic_llong total_delete_aux_local;
  atomic_llong total_delete_remote_domain;
  atomic_llong total_delete_remote_nolock;
  atomic_llong total_modify;
  atomic_llong total_modify_slow;
  atomic_llong total_scanning_work_minor;
  atomic_llong total_scanning_work_major;
  atomic_llong setup_time;
  atomic_llong time_counter_calls;
  atomic_llong total_minor_time;
  atomic_llong total_major_time;
  atomic_llong peak_minor_time;
  atomic_llong peak_major_time;
  atomic_llong total_alloced_pools;
  atomic_llong total_emptied_pools;
  atomic_llong total_freed_pools;
  atomic_llong live_pools; // number of tracked pools
  atomic_llong peak_pools; // max live pools at any time
  atomic_llong ring_operations; // Number of times p->next is mutated
  atomic_llong young_hit_gen; /* number of times a young value was encountered
                           during generic scanning (not minor collection) */
  atomic_llong young_hit_young; /* number of times a young value was encountered
                             during young scanning (minor collection) */
  atomic_llong get_pool_header; // number of times get_pool_header was called
  atomic_llong is_pool_member; // number of times is_pool_member was called
  atomic_llong old_reordering; // pool accesses done to reorder pools
                               // at the occasion of minor scanning
  atomic_llong old_reordering_time; // duration for reordering old
                                      // pools at the occasion of
                                      // minor scanning
} stats;

/* }}} */

/* {{{ Tests in the hot path */

// hot path
/* ownership required: none */
static inline pool * get_pool_header(bxr_slot_ref s)
{
  if (BOXROOT_DEBUG) STATS_INCR(get_pool_header);
  return (pool *)Bxr_get_pool_header(s);
}

// Return true iff v shares the same msbs as p and is not an
// immediate.
// hot path
/* ownership required: none */
static inline bool is_pool_member(bxr_slot v, pool *p)
{
  if (BOXROOT_DEBUG) STATS_INCR(is_pool_member);
  return (uintptr_t)p == ((uintptr_t)v.as_slot_ref & ~((uintptr_t)BXR_POOL_SIZE - 2));
}

// hot path
static inline bool is_empty_free_list(bxr_slot_ref v, pool *p)
{
  return (v == (bxr_slot_ref)p);
}

/* }}} */

/* {{{ Delayed free list data structure */

/* delayed_fl.a_next is the offset in bytes to the start of the pool */
static_assert(BXR_POOL_LOG_SIZE <= sizeof(halfptr_t) * 8, "BXR_POOL_LOG_SIZE too large");

static delayed_free_list make_delayed_fl(pool *p,
                                         bxr_slot_ref next,
                                         int dealloc_count)
{
  /* count in bytes to optim codegen */
  return (delayed_free_list) { .a_next = (char *)next - (char *)p,
                               .a_dealloc_count = dealloc_count };
}

static void extract_delayed_fl(delayed_free_list val,
                               pool *p,
                               bxr_slot_ref *out_next,
                               int *out_dealloc_count)
{
  *out_next = (bxr_slot_ref)((char *)p + val.a_next);
  *out_dealloc_count = val.a_dealloc_count;
}

static const delayed_free_list empty_delayed_fl =
  { .a_next = 0, .a_dealloc_count = 0 };

/* }}} */

/* {{{ Ring operations */

/* ownership required: ring */
static inline void ring_link(pool *p, pool *q)
{
  p->next = q;
  q->prev = p;
  if (BOXROOT_DEBUG) STATS_INCR(ring_operations);
}

/* insert the ring [source] at the back of [*target]. */
/* ownership required: rings */
static inline void ring_push_back(pool *source, pool **target)
{
  if (source == NULL) return;
  DEBUGassert(source->prev == source && source->next == source);
  DEBUGassert(source != *target);
  if (*target == NULL) {
    *target = source;
  } else {
    DEBUGassert((*target)->free_list.classe == source->free_list.classe);
    pool *target_last = (*target)->prev;
    pool *source_last = source->prev;
    ring_link(target_last, source);
    ring_link(source_last, *target);
  }
}

// remove the first element from [*target] and return it
/* ownership required: rings */
static pool * ring_pop(pool **target)
{
  pool *front = *target;
  DEBUGassert(front != NULL);
  if (front->next == front) {
    *target = NULL;
  } else {
    *target = front->next;
    ring_link(front->prev, front->next);
  }
  ring_link(front, front);
  return front;
}

// remove pool [p] from ring [source]
static pool * ring_remove(pool **source, pool *p)
{
  pool **new_source = (p == *source) ? source : &p;
  return ring_pop(new_source);
}

/* }}} */

static long long time_counter(void);

/* {{{ Pool management */

/* the empty free-list for a pool p is denoted by a pointer to the
   pool itself (NULL could be a valid value for an element slot) */
/* ownership required: none */
static inline bxr_slot_ref empty_free_list(pool *p) { return (bxr_slot_ref)p; }

/* ownership required: pool */
static inline bool is_full_pool(pool *p)
{
  return is_empty_free_list(p->free_list.next, p);
}

/* ownership required: none */
static pool * get_empty_pool()
{
  pool *p = bxr_alloc_uninitialised_pool(BXR_POOL_SIZE);
  if (p == NULL) return NULL;
  if (BOXROOT_STATS) {
    long long live_pools = 1 + incr(&stats.live_pools);
    /* racy, but whatever */
    if (live_pools > stats.peak_pools) stats.peak_pools = live_pools;
  }
  STATS_INCR(total_alloced_pools);
  ring_link(p, p);
  p->free_list.next = p->roots;
  p->free_list.alloc_count = 0;
  p->free_list.domain_id = -1;
  p->free_list.classe = UNTRACKED;
  store_relaxed(&p->delayed_fl, empty_delayed_fl);
  bxr_initialize_mutex(&p->mutex);
  /* We end the free_list with a dummy value which satisfies is_pool_member */
  p->roots[POOL_CAPACITY - 1].as_slot_ref = empty_free_list(p);
  for (bxr_slot_ref s = p->roots + POOL_CAPACITY - 2; s >= p->roots; --s) {
    s->as_slot_ref = s + 1;
  }
  return p;
}

/* ownership required: ring */
static void free_pool_ring(pool **ring)
{
  while (*ring != NULL) {
    pool *p = ring_pop(ring);
    bxr_free_pool(p);
    STATS_INCR(total_freed_pools);
  }
}

/* ownership required: rings */
static void free_pool_rings(bxr_domain_state *bxr_dom_st)
{
  free_pool_ring(&bxr_dom_st->old);
  free_pool_ring(&bxr_dom_st->young);
  free_pool_ring(&bxr_dom_st->current);
  free_pool_ring(&bxr_dom_st->free);
}

/* }}} */

/* {{{ Pool class management */

/* ownership required: STW (or the current domain lock + knowledge
   that no other thread owns slots) */
/* Racy over-approximation of the allocation count including delayed
   deallocations. Non-racy when compared to 0. */
static int anticipated_alloc_count(pool *p)
{
  delayed_free_list dfl = load_relaxed(&p->delayed_fl);
  return p->free_list.alloc_count - dfl.a_dealloc_count;
}

/* ownership required: pool */
/* Determines if a pool should be placed towards the front or the back
   of a ring during reclassifying. Takes the delayed deallocation
   count into account. */
static inline bool is_not_too_full(pool *p)
{
  return anticipated_alloc_count(p) <= (int)(BXR_DEALLOC_THRESHOLD / sizeof(bxr_slot));
}

/* Change the current pool from NULL to p */
/* ownership required: domain, pool */
static void set_current_pool(int dom_id, pool *p)
{
  bxr_domain_state *local = get_bxr_domain_state(dom_id);
  DEBUGassert(local->current == NULL);
  if (p == NULL) return;
  DEBUGassert(p->next == p);
  p->free_list.domain_id = dom_id;
  local->current = p;
  p->free_list.classe = YOUNG;
  /* We prevent the current pool from triggering a slow deallocation
     path when empty by lying on its alloc count (never 0). */
  p->free_list.alloc_count++;
  set_current_fl(local, &p->free_list);
}

static void reclassify_pool(pool **source, int dom_id, int cl);
static int reclassify_ring(pool **ring, int dom_id, int cl);

/* Empty the current pool ring onto the young pool ring. */
static void move_current_to_young(int dom_id)
{
  bxr_domain_state *local = get_bxr_domain_state(dom_id);
  if (local->current != NULL) {
    pool *p = ring_pop(&local->current);
    /* Undo the increment inside set_current_pool */
    p->free_list.alloc_count--;
    // Heuristic: if a current pool has just been allocated, we ensure
    // that it is the first one to be considered the next time a young
    // boxroot allocation takes place. It is added to the front and
    // stays to the front after reclassifications.
    reclassify_pool(&p, dom_id, YOUNG);
    set_current_fl(local, empty_fl_ptr);
  }
}

/* Move not-too-full pools to the front; move empty pools to the free
   ring. */
/* ownership required: domain, pool */
static void try_demote_pool(int dom_id, pool *p)
{
  DEBUGassert(p->free_list.classe != UNTRACKED);
  bxr_domain_state *local = get_bxr_domain_state(dom_id);
  if (p == local->current || !is_not_too_full(p)) return;
  int cl = (anticipated_alloc_count(p) == 0) ? UNTRACKED : p->free_list.classe;
  /* If the pool is at the head of its ring, the new head must be
     recorded. */
  pool **source = (p == local->old) ? &local->old :
                  (p == local->young) ? &local->young : &p;
  reclassify_pool(source, dom_id, cl);
}

static void validate_pool(pool *pl);

/* ownership required: domain */
/* Assumes that the pool is full. */
static void flush_delayed_fl(pool *p)
{
  DEBUGassert(is_full_pool(p));
  /* synchronise with free_slot_atomic */
  delayed_free_list fl = atomic_exchange_explicit(&p->delayed_fl, empty_delayed_fl,
                                                  memory_order_acquire);
  bxr_slot_ref delayed_next;
  int dealloc_count;
  extract_delayed_fl(fl, p, &delayed_next, &dealloc_count);
  /* single consumer, hence no ABA */
  p->free_list.next = delayed_next;
  p->free_list.alloc_count = POOL_CAPACITY - dealloc_count;
}

/* Take the first pool that is not full provided it is flushed. Since
   pools are moved to the front when they are freed by local
   deallocation, this favours pools in use on the current thread; it
   considers pending remote deallocations as a secondary choice. */
/* ownership required: ring */
static inline pool * pop_available(pool **target)
{
  pool *start = *target;
  if (start == NULL) return NULL;
  pool *p = start;
  do {
    if (anticipated_alloc_count(p) < POOL_CAPACITY)
      return ring_remove(target, p);
    p = p->next;
  } while (p != start);
  return NULL;
}

static void reorder_old_pools(int dom_id);

/* Find an available pool. It returns NULL and sets errno to ENOMEM if
   no available pool was found and the allocation of a new one
   failed. */
/* ownership required: domain */
static pool * get_available_pool(int dom_id)
{
  bxr_domain_state *local = get_bxr_domain_state(dom_id);
  /* First try to find a young pool with some space available */
  pool *p = pop_available(&local->young);
  if (p == NULL && local->old != NULL) {
    /* When pools empty themselves enough, they are moved to the front
       of their ring. So if the first old pool is too full, then so are the
       subsequent ones.

       Delayed deallocations inside old pools are only taken into
       account once per minor collection. Given that pools become old
       at minor collection, this is enough to avoid blow-up under
       producer-consumer scenarios. */
    if (!is_not_too_full(local->old) && !local->reordered_since_minor) {
      local->reordered_since_minor = true;
      reorder_old_pools(dom_id);
    }
    if (is_not_too_full(local->old))
      p = ring_pop(&local->old);
  }
  if (p == NULL && local->free != NULL) p = ring_pop(&local->free);
  if (p == NULL) p = get_empty_pool();
  /* the young, old, or free pool might be full with pending
     deallocations. */
  if (is_full_pool(p)) flush_delayed_fl(p);
  DEBUGassert(!is_full_pool(p));
  return p;
}

static void validate_all_pools(int dom_id);

/* move the head of [source] to the appropriate ring in domain
   [dom_id] determined by [classe]. Not-too-full pools are pushed to
   the front. */
/* ownership required: ring, domain */
static void reclassify_pool(pool **source, int dom_id, int cl)
{
  DEBUGassert(*source != NULL);
  bxr_domain_state *local = get_bxr_domain_state(dom_id);
  pool *p = ring_pop(source);
  p->free_list.domain_id = dom_id;
  pool **target = NULL;
  switch (cl) {
  case OLD: target = &local->old; break;
  case YOUNG: target = &local->young; break;
  case UNTRACKED:
    target = &local->free;
    DEBUGassert(anticipated_alloc_count(p) == 0);
    STATS_INCR(total_emptied_pools);
    STATS_DECR(live_pools);
    break;
  }
  /* protected by domain lock */
  p->free_list.classe = cl;
  ring_push_back(p, target);
  /* make p the new head of [*target] (rotate one step backwards) if
     it is not too full. */
  if (is_not_too_full(p)) *target = p;
}

/* Reclassify a full ring while maintaining ordering */
static int reclassify_ring(pool **source, int dom_id, int cl)
{
  pool *ring = *source;
  int work = 0;
  *source = NULL;
  while (ring != NULL) {
    // LIFO
    ring = ring->prev;
    reclassify_pool(&ring, dom_id, cl);
    work++;
  }
  return work;
}

  /* Reorder old pools, to take the delayed deallocation count into
     account. */
static void reorder_old_pools(int dom_id)
{
  bxr_domain_state *local = get_bxr_domain_state(dom_id);
  long long reorder_start = time_counter();
  int reordered = reclassify_ring(&local->old, dom_id, OLD);
  if (BOXROOT_STATS) {
    long long reorder_duration = time_counter() - reorder_start;
    stats.old_reordering += reordered;
    stats.old_reordering_time += reorder_duration;
  }
}


/* }}} */

/* {{{ Allocation, deallocation */

/* Thread-safety: see documented constraints on the use of
   boxroot_setup and boxroot_teardown. */
static atomic_int status = BOXROOT_NOT_SETUP;

int boxroot_status()
{
  return load_relaxed(&status);
}

static bool setup();

// Set an available pool as current and allocate from it.
/* ownership required: none */
boxroot bxr_create_slow(value init)
{
  STATS_INCR(total_create_slow);
  long long time = time_counter();
  if (Caml_state_opt == NULL) { errno = EPERM; return NULL; }
  // We might be here because boxroot is not setup.
  if (!setup()) return NULL;
#if !OCAML_MULTICORE
  if (!bxr_domain_lock_held()) { errno = EPERM; return NULL; }
  /* Check the thread hooks after checking the runtime lock is held.
     In the normal case, `bxr_check_thread_hooks` requires the runtime
     lock to be held; in the failure case, all bets are off anyway. */
  if (!bxr_check_thread_hooks()) {
    status = BOXROOT_INVALID;
    return NULL;
  }
#endif
  int dom_id = Domain_id;
  /* Perhaps we are here only because the boxroot domain state was not
     cached in TLS. Initialise the thread-local state (and thus also
     the domain-local state if needed), and try again. */
  if (!thread_initialised()) {
    if (!init_thread(dom_id)) return NULL; /* ENOMEM */
    return boxroot_create(init);
  }
  bxr_domain_state *local = get_bxr_domain_state(dom_id);
  DEBUGassert(local != NULL);
  if (local->current != NULL) {
    /* Necessarily we are here because the pool is full. We make room
       on local->current. */
    DEBUGassert(is_full_pool(local->current));
  }
  /* The current delayed free list might be non-empty, but we do not
     want to flush it yet. We always look for another pool, either
     because the pool is completely full, or in order to avoid
     contended scenarios where a consumer races to refill the same
     delayed free list that we would be flushing repeatedly. */
  pool *available = get_available_pool(dom_id);
  if (available == NULL) return NULL; /* ENOMEM */
  move_current_to_young(dom_id);
  set_current_pool(dom_id, available);
  /* Try again; this should succeed */
  boxroot res = boxroot_create(init);
  if (BOXROOT_STATS) stats.total_create_slow_time += time_counter() - time;
  return res;
}

/* }}} */

/* {{{ Boxroot API implementation */

extern inline value boxroot_get(boxroot root);
extern inline value const * boxroot_get_ref(boxroot root);

/* ownership required: current domain */
void bxr_create_debug(value init)
{
  DEBUGassert(Caml_state_opt != NULL);
  if (Is_block(init) && Is_young(init)) STATS_INCR(total_create_young);
  else STATS_INCR(total_create_old);
}

extern inline boxroot boxroot_create(value init);

/* Needed to avoid linking error with Rust */
extern inline bool bxr_free_slot(bxr_free_list *fl, boxroot root);

/* ownership required: root, current domain */
void bxr_delete_debug(boxroot root)
{
  DEBUGassert(root != NULL);
  value v = boxroot_get(root);
  if (Is_block(v) && Is_young(v)) STATS_INCR(total_delete_young);
  else STATS_INCR(total_delete_old);
}

/* ownership required: root plus any domain lock or the pool mutex */
static void free_slot_atomic(pool *p, boxroot root)
{
  /* Lock-free MPSC stack.

     The race with root scanning is handled either by having a domain
     lock, or by locking the pool mutex. */
  bxr_slot_ref new_next = &root->contents;
  delayed_free_list old_fl = load_relaxed(&p->delayed_fl);
  bxr_slot_ref old_next;
  int old_dealloc_count;
  delayed_free_list new_fl;
  do {
    extract_delayed_fl(old_fl, p, &old_next, &old_dealloc_count);
    new_fl = make_delayed_fl(p, new_next, old_dealloc_count + 1);
    new_next->as_slot_ref = old_next;
  } while (!atomic_compare_exchange_weak_explicit(&p->delayed_fl,
                                                  &old_fl, new_fl,
                                                  memory_order_release,
                                                  memory_order_relaxed));
}

/* ownership required: root, current domain */
void bxr_delete_aux(boxroot root, bxr_free_list *fl, bool remote)
{
  pool *p = (pool *)fl;
  if (!remote) {
    STATS_INCR(total_delete_aux_local);
    /* We own the domain lock. Deallocation already done, but we
       passed a deallocation threshold. */
    try_demote_pool(p->free_list.domain_id, p);
  } else if (OCAML_MULTICORE && bxr_domain_lock_held()) {
    if (BOXROOT_DEBUG) STATS_INCR(total_delete_remote_domain);
    /* Remote, from another domain. */
    free_slot_atomic(p, root);
  } else {
    /* No domain lock held. We need to lock the pool mutex to avoid
       races with the GC. */
    if (BOXROOT_DEBUG) STATS_INCR(total_delete_remote_nolock);
    bxr_mutex_lock(&p->mutex);
    free_slot_atomic(p, root);
    bxr_mutex_unlock(&p->mutex);
  }
}

extern inline void boxroot_delete(boxroot root);

/* ownership required: root, current domain */
bool bxr_modify_slow(boxroot *root_ref, value new_value)
{
  STATS_INCR(total_modify_slow);
  if (!bxr_domain_lock_held()) { errno = EPERM; return false; }
  /* The pool is old, so we reallocate the root. This can happen only
     once per minor collection per root. */
  boxroot new = boxroot_create(new_value);
  if (BXR_UNLIKELY(new == NULL)) return false;
  boxroot old = *root_ref;
  *root_ref = new;
  boxroot_delete(old);
  return true;
}

void bxr_modify_debug(boxroot *rootp)
{
  DEBUGassert(*rootp);
  STATS_INCR(total_modify);
}

extern inline bool boxroot_modify(boxroot *rootp, value new_value);

/* }}} */

/* {{{ Scanning */

static void validate_fl(pool *pl, bxr_slot_ref curr, int length)
{
  int pos = 0;
  for (; curr != empty_free_list(pl); curr = curr->as_slot_ref, pos++)
  {
    assert(pos < POOL_CAPACITY);
    assert(curr >= pl->roots && curr < pl->roots + POOL_CAPACITY);
  }
  DEBUGassert(pos == length);
}

/* ownership required: STW (races with remote deallocation) */
static void validate_pool(pool *pl)
{
  if (pl->free_list.next == NULL) {
    // an unintialised pool
    assert(pl->free_list.classe == UNTRACKED);
    return;
  }
  // check free_list structure and length
  validate_fl(pl, pl->free_list.next, POOL_CAPACITY - pl->free_list.alloc_count);
  // check delayed_fl structure and length
  bxr_slot_ref delayed_next;
  int dealloc_count;
  extract_delayed_fl(pl->delayed_fl, pl, &delayed_next, &dealloc_count);
  validate_fl(pl, delayed_next, dealloc_count);
  // check count of allocated elements
  int count = 0;
  for(int i = 0; i < POOL_CAPACITY; i++) {
    bxr_slot s = pl->roots[i];
    STATS_DECR(is_pool_member); // Validation should not interfere with stats
    if (!is_pool_member(s, pl)) {
      value v = s.as_value;
      if (pl->free_list.classe != YOUNG && Is_block(v)) assert(!Is_young(v));
      ++count;
    }
  }
  assert(count == anticipated_alloc_count(pl));
}

/* ownership required: STW (races with remote deallocation) */
static void validate_ring(pool **ring, int dom_id, int cl)
{
  pool *start_pool = *ring;
  if (start_pool == NULL) return;
  pool *p = start_pool;
  do {
    assert(p->free_list.domain_id == dom_id);
    assert(p->free_list.classe == cl);
    validate_pool(p);
    assert(p->next != NULL);
    assert(p->next->prev == p);
    assert(p->prev != NULL);
    assert(p->prev->next == p);
    p = p->next;
  } while (p != start_pool);
}

/* ownership required: STW (races with remote deallocation) */
static void validate_current_pool(pool **current, int dom_id)
{
  if (*current != NULL) {
    assert((*current)->next == *current && (*current)->prev == *current);
    /* Temporarily fix the alloc count for the current pool, see
       set_current_pool. */
    (*current)->free_list.alloc_count--;
  }
  validate_ring(current, dom_id, YOUNG);
  if (*current != NULL) (*current)->free_list.alloc_count++;
}

/* ownership required: STW (races with remote deallocation) */
static void validate_all_pools(int dom_id)
{
  bxr_domain_state *local = get_bxr_domain_state(dom_id);
  if (local == NULL) return;
  validate_ring(&local->old, dom_id, OLD);
  validate_ring(&local->young, dom_id, YOUNG);
  validate_current_pool(&local->current, dom_id);
  validate_ring(&local->free, dom_id, UNTRACKED);
}

/* ownership required: domain (maybe uninit) */
static void orphan_pools(int dom_id)
{
  bxr_domain_state *local = get_bxr_domain_state(dom_id);
  if (local == NULL) return;
  move_current_to_young(dom_id);
  bxr_mutex_lock(&orphan_mutex);
  /* Move active pools to the orphaned pools. */
  ring_push_back(local->old, &orphan.old);
  ring_push_back(local->young, &orphan.young);
  bxr_mutex_unlock(&orphan_mutex);
  /* Free the rest */
  free_pool_ring(&local->free);
  /* Reset local pools for later domains spawning with the same id */
  init_pool_rings(local);
}

/* ownership required: domain */
static void adopt_orphaned_pools(int dom_id)
{
  bxr_mutex_lock(&orphan_mutex);
  reclassify_ring(&orphan.old, dom_id, OLD);
  reclassify_ring(&orphan.young, dom_id, YOUNG);
  bxr_mutex_unlock(&orphan_mutex);
}

// returns the amount of work done
/* ownership required: STW and pool mutex */
static inline int scan_pool_aux(scanning_action action, int only_young, void *data, pool *pl)
{
  int allocs_to_find = anticipated_alloc_count(pl);
  int young_hit = 0;
  bxr_slot_ref current = pl->roots;
  minor_heap_info heap_info = get_minor_heap_info();
  while (allocs_to_find) {
    DEBUGassert(current < &pl->roots[POOL_CAPACITY]);
    // hot path
    bxr_slot s = *current;
    if (!is_pool_member(s, pl)) {
      --allocs_to_find;
      value v = s.as_value;
      if (BOXROOT_DEBUG && Bxr_is_young(heap_info, v)) ++young_hit;
      /* Pre-filter values when [only_young].

         Benchmark results for minor scanning (without early-exit optimisation):
         20% faster for young hits=95%
         20% faster for young hits=50% (random)
         90% faster for young_hits=10% (random)
         280% faster for young hits=0%
      */
      if (!only_young || Bxr_is_young(heap_info, v))
        CALL_GC_ACTION(action, data, v, &current->as_value);
    }
    ++current;
  }
  if (BOXROOT_STATS) {
    if (only_young) stats.young_hit_young += young_hit;
    else stats.young_hit_gen += young_hit;
  }
  return current - pl->roots;
}

/* The following two functions are never inlined in order to have an
   easily scrutinizable and more predictable code generation. */

Noinline static int scan_pool_young(scanning_action action, void *data, pool *pl)
{
  return scan_pool_aux(action, true, data, pl);
}

Noinline static int scan_pool_gen(scanning_action action, void *data, pool *pl)
{
  return scan_pool_aux(action, false, data, pl);
}

static int scan_pool(scanning_action action, int only_young, void *data, pool *pl)
{
  int res;
  bxr_mutex_lock(&pl->mutex);
  if (only_young) {
    res = scan_pool_young(action, data, pl);
  } else {
    res = scan_pool_gen(action, data, pl);
  }
  bxr_mutex_unlock(&pl->mutex);
  return res;
}

/* ownership required: STW */
static int scan_ring(scanning_action action, int only_young,
                     void *data, pool **ring)
{
  int work = 0;
  pool *start_pool = *ring;
  if (start_pool == NULL) return 0;
  pool *p = start_pool;
  do {
    work += scan_pool(action, only_young, data, p);
    p = p->next;
  } while (p != start_pool);
  return work;
}

/* ownership required: STW */
static int scan_pools(scanning_action action, int only_young,
                      void *data, int dom_id)
{
  bxr_domain_state *local = get_bxr_domain_state(dom_id);
  int work = scan_ring(action, only_young, data, &local->young);
  if (!only_young) work += scan_ring(action, 0, data, &local->old);
  if (bxr_in_minor_collection()) {
    /* Promote non-empty young pools as old pools */
    reclassify_ring(&local->young, dom_id, OLD);
    /* Reorder according to delayed deallocation count once per
       minor */
    local->reordered_since_minor = false;
  } else {
    free_pool_ring(&local->free);
  }
  return work;
}

/* ownership required: STW */
static void scan_roots(scanning_action action, int only_young,
                       void *data, int dom_id)
{
  if (BOXROOT_DEBUG) validate_all_pools(dom_id);
  move_current_to_young(dom_id);
  /* The first domain arriving there will take ownership of the pools
     of terminated domains. */
  adopt_orphaned_pools(dom_id);
  int work = scan_pools(action, only_young, data, dom_id);
  if (BOXROOT_STATS) {
    if (only_young) stats.total_scanning_work_minor += work;
    else stats.total_scanning_work_major += work;
  }
  if (BOXROOT_DEBUG) validate_all_pools(dom_id);
}

/* }}} */

/* {{{ Statistics */

/* Overhead of 20ns or more with TSC */
static long long time_counter(void)
{
#if defined(POSIX_CLOCK) && BOXROOT_STATS
  STATS_INCR(time_counter_calls);
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (long long)t.tv_sec * (long long)1000000000 + (long long)t.tv_nsec;
#else
  return 0;
#endif
}

// unit: 1=KiB, 2=MiB
static long long kib_of_pools(long long count, int unit)
{
  int log_per_pool = BXR_POOL_LOG_SIZE - unit * 10;
  if (log_per_pool >= 0) return count << log_per_pool;
  else return count >> -log_per_pool;
}

static double average(long long total, long long units)
{
  // round to nearest
  return ((double)total) / (double)units;
}

/* ownership required: none */
void boxroot_print_stats()
{
  printf("- minor collections: %'lld\n"
         "  major collections (and others): %'lld\n",
         stats.minor_collections,
         stats.major_collections);

#if defined(POSIX_CLOCK)
  long long total_time_ns = time_counter() - stats.setup_time;
  double total_time = (double)total_time_ns / 1000;

  printf("  time since setup: %'.0fµs\n"
         "  incl. time counter calls: %'lld\n",
         total_time, stats.time_counter_calls);
#endif

  if (stats.total_alloced_pools == 0) return;

#if defined(POSIX_CLOCK)
  double total_minor = (double)stats.total_minor_time / 1000;
  double total_major = (double)stats.total_major_time / 1000;
  double pct_minor = average(stats.total_minor_time, total_time_ns) * 100;
  double pct_major = average(stats.total_major_time, total_time_ns) * 100;

  double time_scan = total_minor + total_major;
  double pct_scan = average(time_scan, total_time) * 100;
  double time_minus_scan = total_time - time_scan;
  double pct_minus_scan = average(time_minus_scan, total_time) * 100;

  printf("  minor scan time: %'.0fµs (%.2f%%)\n"
         "  major scan time: %'.0fµs (%.2f%%)\n"
         "  time scanning: %'.0fµs (%.2f%%)\n"
         "  time minus scanning: %'.0fµs (%.2f%%)\n",
         total_minor, pct_minor,
         total_major, pct_major,
         time_scan, pct_scan,
         time_minus_scan, pct_minus_scan);
#endif

  printf("- BXR_POOL_LOG_SIZE: %d (%'lld KiB, %'d roots/pool)\n"
         "  BOXROOT_STATS: %d\n"
         "  BOXROOT_DEBUG: %d\n"
         "  OCAML_MULTICORE: %d\n"
         "  BXR_MULTITHREAD: %d\n"
         "  BXR_FORCE_REMOTE: %d\n",
         (int)BXR_POOL_LOG_SIZE, kib_of_pools(1, 1), (int)POOL_CAPACITY,
         (int)BOXROOT_STATS, (int)BOXROOT_DEBUG, (int)OCAML_MULTICORE,
         (int)BXR_MULTITHREAD, (int)BXR_FORCE_REMOTE);

  printf("- total allocated pools: %'lld (%'lld MiB)\n"
         "  peak allocated pools: %'lld (%'lld MiB)\n"
         "  total emptied pools: %'lld (%'lld MiB)\n"
         "  total freed pools: %'lld (%'lld MiB)\n",
         stats.total_alloced_pools,
         kib_of_pools(stats.total_alloced_pools, 2),
         stats.peak_pools,
         kib_of_pools(stats.peak_pools, 2),
         stats.total_emptied_pools,
         kib_of_pools(stats.total_emptied_pools, 2),
         stats.total_freed_pools,
         kib_of_pools(stats.total_freed_pools, 2));

  double scanning_work_minor =
    average(stats.total_scanning_work_minor, stats.minor_collections);
  double scanning_work_major =
    average(stats.total_scanning_work_major, stats.major_collections);
  long long total_scanning_work =
    stats.total_scanning_work_minor + stats.total_scanning_work_major;

#if defined(POSIX_CLOCK)
  double scanning_pace =
    average(stats.total_minor_time + stats.total_major_time,
            stats.total_scanning_work_minor + stats.total_scanning_work_major);
  double scanning_pace_minor =
    average(stats.total_minor_time, stats.total_scanning_work_minor);
  double scanning_pace_major =
    average(stats.total_major_time, stats.total_scanning_work_major);
#endif

#if BOXROOT_DEBUG
  double young_hits_gen_pct =
    average(stats.young_hit_gen * 100, stats.total_scanning_work_major);
#endif
  double young_hits_young_pct =
    average(stats.young_hit_young * 100, stats.total_scanning_work_minor);

  printf("- work per minor: %'.0f\n"
         "  work per major: %'.0f\n"
         "  total scanning work: %'lld (%'lld minor, %'lld major)\n"
#if defined(POSIX_CLOCK)
         "  total scanning pace (ns per work): %'.2f (%'.2f minor, %'.2f major)\n"
#endif
#if BOXROOT_DEBUG
         "  young hits (non-minor collection): %.2f%%\n"
#endif
         "  young hits (minor collection): %.2f%%\n",
         scanning_work_minor,
         scanning_work_major,
         total_scanning_work, stats.total_scanning_work_minor, stats.total_scanning_work_major,
#if defined(POSIX_CLOCK)
         scanning_pace, scanning_pace_minor, scanning_pace_major,
#endif
#if BOXROOT_DEBUG
         young_hits_gen_pct,
#endif
         young_hits_young_pct);

#if defined(POSIX_CLOCK)
  double time_per_minor =
    average(stats.total_minor_time, stats.minor_collections) / 1000;
  double time_per_major =
    average(stats.total_major_time, stats.major_collections) / 1000;

  printf("- average scan time per minor: %'.3fµs\n"
         "  average scan time per major: %'.3fµs\n"
         "  peak time per minor: %'.3fµs\n"
         "  peak time per major: %'.3fµs\n",
         time_per_minor,
         time_per_major,
         ((double)stats.peak_minor_time) / 1000,
         ((double)stats.peak_major_time) / 1000);
#endif

  printf("- total boxroot_create_slow: %'lld\n"
         "  total boxroot_modify_slow: %'lld\n"
         "  total boxroot_delete_aux local: %'lld\n",
         stats.total_create_slow,
         stats.total_modify_slow,
         stats.total_delete_aux_local);

  double old_reordering_per_minor =
    average(stats.old_reordering, stats.minor_collections);
  double old_reordering_time = (double)stats.old_reordering_time / 1000;
  double old_reordering_time_pct =
    average(stats.old_reordering_time, stats.total_minor_time) * 100;

  printf("  total boxroot_delete_aux remote domain: %'lld\n"
         "  total boxroot_delete_aux remote no domain: %'lld\n"
         "  old pools reordered: %.2f per minor (%'.3fµs total, %.2f%% minor scan time)\n",
         stats.total_delete_remote_domain,
         stats.total_delete_remote_nolock,
         old_reordering_per_minor, old_reordering_time, old_reordering_time_pct);

#if defined(POSIX_CLOCK)
  double create_slow_time = (double)stats.total_create_slow_time / 1000;
  double pct_create = average(stats.total_create_slow_time, total_time_ns) * 100;

  printf("  boxroot_create_slow time: %'.0fµs (%.2f%%)\n",
         create_slow_time, pct_create);
#endif

#if BOXROOT_DEBUG

  double ring_operations_per_pool =
    average(stats.ring_operations, stats.total_alloced_pools);

  printf("- total ring operations: %'lld\n"
         "  ring operations per pool: %.2f\n",
         stats.ring_operations,
         ring_operations_per_pool);

  long long total_create = stats.total_create_young + stats.total_create_old;
  long long total_delete = stats.total_delete_young + stats.total_delete_old;
  double create_young_pct =
    average(stats.total_create_young * 100, total_create);
  double delete_young_pct =
    average(stats.total_delete_young * 100, total_delete);

  printf("  total created: %'lld (%.2f%% young)\n"
         "  total deleted: %'lld (%.2f%% young)\n"
         "  total modified: %'lld\n",
         total_create, create_young_pct,
         total_delete, delete_young_pct,
         stats.total_modify);

  printf("  is_pool_member: %'lld\n",
         stats.is_pool_member);
#endif
}

/* }}} */

/* {{{ Hook setup */

/* ownership required: STW */
static void scanning_callback(scanning_action action, int only_young,
                              void *data)
{
  if (boxroot_status() == BOXROOT_NOT_SETUP
      || boxroot_status() == BOXROOT_TORE_DOWN) return;
  bool in_minor_collection = bxr_in_minor_collection();
  if (in_minor_collection) STATS_INCR(minor_collections);
  else STATS_INCR(major_collections);
  int dom_id = Domain_id;
  if (get_bxr_domain_state(dom_id) == NULL) return; /* synchronised by domain lock */
#if !OCAML_MULTICORE
  if (!bxr_check_thread_hooks()) status = BOXROOT_INVALID;
#endif
  long long start = time_counter();
  scan_roots(action, only_young, data, dom_id);
  long long duration = time_counter() - start;
  if (BOXROOT_STATS) {
    atomic_llong *total = in_minor_collection ? &stats.total_minor_time : &stats.total_major_time;
    atomic_llong *peak = in_minor_collection ? &stats.peak_minor_time : &stats.peak_major_time;
    *total += duration;
    if (duration > *peak) *peak = duration; // racy, but whatever
  }
}

/* Handle orphaning of domain-local pools */
/* ownership required: current domain */
static void domain_termination_callback()
{
  DEBUGassert(OCAML_MULTICORE == 1);
  int dom_id = Domain_id;
  orphan_pools(dom_id);
}

/* Used for initialization/teardown */
static mutex_t init_mutex = BXR_MUTEX_INITIALIZER;

/* ownership required: current domain */
static bool setup()
{
  /* Ensure the domain lock is held (OCaml 5) */
  if (Caml_state_opt == NULL) {
    errno = EPERM;
    return false;
  }
  if (boxroot_status() == BOXROOT_RUNNING) return true;
  bool res = true;
  bxr_mutex_lock(&init_mutex);
  if (status != BOXROOT_NOT_SETUP) {
    res = (status == BOXROOT_RUNNING);
    goto out;
  }
#if !OCAML_MULTICORE
  /* With OCaml < 5.0, runtime lock detection must be setup before any
     thread is created, otherwise it does not work. It must also be
     installed after threads initialization. In addition, [setup] must
     be called whenever one cannot guarantee that the first boxroot
     allocation runs while holding the lock. */
  bxr_init_systhreads();
  /* Note: with OCaml >= 5.0, we cannot call an OCaml function due to
     lock inversion (if it triggers a STW). Systhread init can also
     raise an exception into OCaml, which is unsound here. Also, it is
     not necessary to call it. */
#endif
  init_bxr_domain_state();
  bxr_setup_hooks(&scanning_callback, &domain_termination_callback);
  stats.setup_time = time_counter();
  // we are done
  status = BOXROOT_RUNNING;
  // fall through
 out:
  bxr_mutex_unlock(&init_mutex);
  return res;
}

/* It is unnecessary to call boxroot_setup directly with OCaml 5. */
bool boxroot_setup(void) { return setup(); }

/* We are sole owner of the pools at this point, no need for
   locking. */
void boxroot_teardown()
{
  bxr_mutex_lock(&init_mutex);
  if (status != BOXROOT_RUNNING) goto out;
  status = BOXROOT_TORE_DOWN;
  free_domain_state();
  free_pool_rings(&orphan);
  // fall through
 out:
  bxr_mutex_unlock(&init_mutex);
}

char const * boxroot_error_string(void)
{
  int status = boxroot_status();
  switch (status) {
  case BOXROOT_TORE_DOWN: return "boxroot_teardown has previously been called";
  case BOXROOT_INVALID: return "Ensure boxroot_setup() is called as documented";
  case BOXROOT_RUNNING:
  case BOXROOT_NOT_SETUP:
    if (errno == EPERM) {
      return "You tried calling boxroot_create, boxroot_modify, or boxroot_setup "
             "without holding the domain lock";
    } else if (errno == ENOMEM) {
      return "Allocation failure of the backing store";
    }
    // fall through
  default:
    return "Unknown error";
  }
}

/* }}} */

/* {{{ */
/* }}} */
