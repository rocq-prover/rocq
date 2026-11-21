/* SPDX-License-Identifier: MIT */
#ifndef BOXROOT_PLATFORM_H
#define BOXROOT_PLATFORM_H

#define CAML_NAME_SPACE

#ifndef __cplusplus
#include <stdbool.h>
#include <stdint.h>
#else
#include <cstdint>
#endif

#include <caml/config.h>
#include <caml/version.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef intnat value;

#if SIZEOF_PTR == 8 // defined through caml/config.h
typedef uint32_t halfptr_t;
#else
static_assert(SIZEOF_PTR == 4, "Pointers expected 32 or 64 bits.")
typedef uint16_t halfptr_t;
#endif

#if defined(__GNUC__)
#define BXR_LIKELY(a) __builtin_expect(!!(a),1)
#define BXR_UNLIKELY(a) __builtin_expect(!!(a),0)
#else
#define BXR_LIKELY(a) (a)
#define BXR_UNLIKELY(a) (a)
#endif

#if OCAML_VERSION >= 50000
  // Note: contra to convention, caml/domain_state.h is made to be
  // included from inside extern "C" {}
#include <caml/domain_state.h>
#define OCAML_MULTICORE true
#else
#define Caml_state_opt Caml_state
#define OCAML_MULTICORE false
#endif

#ifdef __cplusplus
} // extern "C"
#endif

#ifdef CAML_INTERNALS

#include <assert.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stddef.h>
#include <caml/mlvalues.h>
#include <caml/minor_gc.h>
#include <caml/roots.h>

#if OCAML_MULTICORE
#define Domain_id (Caml_state->id)
#else
#define Domain_id 0
#endif // OCAML_MULTICORE

#define Cache_line_size 64
//#define Cache_line_size 128 /* Apple M1 */

#define load_relaxed(a) (atomic_load_explicit((a), memory_order_relaxed))
#define load_acquire(a) (atomic_load_explicit((a), memory_order_acquire))
#define store_relaxed(a, n) (atomic_store_explicit((a), (n), memory_order_relaxed))
#define incr(a) (atomic_fetch_add_explicit((a), 1, memory_order_relaxed))
#define decr(a) (atomic_fetch_add_explicit((a), -1, memory_order_relaxed))
#define incr_release(a) (atomic_fetch_add_explicit((a), 1, memory_order_release))
#define decr_release(a) (atomic_fetch_add_explicit((a), -1, memory_order_release))

typedef pthread_mutex_t mutex_t;
#define BXR_MUTEX_INITIALIZER PTHREAD_MUTEX_INITIALIZER;

bool bxr_initialize_mutex(mutex_t *mutex);
void bxr_mutex_lock(mutex_t *mutex);
void bxr_mutex_unlock(mutex_t *mutex);

/* Check integrity of pool structure after each scan, and compute
   additional statistics? (slow)
   This can be enabled by passing BOXROOT_DEBUG=1 as argument. */
#ifndef BOXROOT_DEBUG
#define BOXROOT_DEBUG false
#endif

/* Compute some statistics, should have marginal impact on performance
   unless DEBUG == 1. This can be enabled by passing BOXROOT_STATS=1
   as argument. */
#ifndef BOXROOT_STATS
#define BOXROOT_STATS BOXROOT_DEBUG
#endif

#if BOXROOT_STATS
#define STATS_INCR(x) (incr(&stats.x))
#define STATS_DECR(x) (decr(&stats.x))
#else
#define STATS_INCR(x) ((void)(0))
#define STATS_DECR(x) ((void)(0))
#endif

#if BOXROOT_DEBUG
#define DEBUGassert(x) assert(x)
#elif defined(__GNUC__)
#define DEBUGassert(x) do { if (!(x)) { __builtin_unreachable(); } } while (0)
#else
#define DEBUGassert(x) ((void)(x))
#endif

typedef struct pool pool;

pool* bxr_alloc_uninitialised_pool(size_t size);
void bxr_free_pool(pool *p);

#if defined(__GNUC__)
#define Noinline __attribute__((noinline))
#elif defined(_MSC_VER)
#define Noinline __declspec(noinline)
#else
#define Noinline
#endif

#endif // CAML_INTERNALS

#endif // BOXROOT_PLATFORM_H
