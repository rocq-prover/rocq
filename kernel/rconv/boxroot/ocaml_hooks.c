/* SPDX-License-Identifier: MIT */
#define CAML_NAME_SPACE
#define CAML_INTERNALS

#include "ocaml_hooks.h"
#include "platform.h"

#include <assert.h>
#include <limits.h>

#include <caml/misc.h>
#include <caml/minor_gc.h>
#if OCAML_MULTICORE
#include <caml/domain.h>
#endif

static atomic_int in_minor_collection = 0;

static caml_timing_hook prev_minor_begin_hook = NULL;
static caml_timing_hook prev_minor_end_hook = NULL;

/* In OCaml 5.0, in_minor_collection records the number of parallel
   domains currently doing a minor collection.

   Correctness depends on:
   - The stop-the-world (STW) nature of minor collection, and the fact
     that the timing hooks are called inside the STW section.
   - The fact that setup_hooks and scanning_callback are called while
     holding a domain lock. Thus, setup_hooks is called outside of a
     minor collection (in_minor_collection starts at 0 correctly), and
     scanning_callback runs either entirely inside or entirely outside
     of a STW section.
*/

static void record_minor_begin()
{
  incr(&in_minor_collection);
  if (prev_minor_begin_hook != NULL) prev_minor_begin_hook();
}

static void record_minor_end()
{
  decr(&in_minor_collection);
  if (prev_minor_end_hook != NULL) prev_minor_end_hook();
}

bool bxr_in_minor_collection()
{
  return load_relaxed(&in_minor_collection) != 0;
}

static bxr_scanning_callback scanning_callback = NULL;

#if OCAML_MULTICORE

static scan_roots_hook prev_scan_roots_hook = NULL;

static caml_timing_hook domain_terminated_callback = NULL;
static caml_timing_hook prev_domain_terminated_hook = NULL;

static void bxr_scan_hook(scanning_action action, scanning_action_flags flags,
                      void *data, caml_domain_state *dom_st)
{
  if (prev_scan_roots_hook != NULL) {
    (*prev_scan_roots_hook)(action, flags, data, dom_st);
  }
  int only_young = flags & SCANNING_ONLY_YOUNG_VALUES;
  (*scanning_callback)(action, only_young, data);
}

static void domain_terminated_hook()
{
  if (prev_domain_terminated_hook != NULL) {
    (*prev_domain_terminated_hook)();
  }
  (*domain_terminated_callback)();
}

void bxr_setup_hooks(bxr_scanning_callback scanning,
                     caml_timing_hook domain_termination)
{
  scanning_callback = scanning;
  // Save previous hooks and install ours.
  // prev_*_hook synchronized via domain lock since the hooks are called
  // during STW.
  prev_scan_roots_hook = atomic_exchange(&caml_scan_roots_hook,
                                         bxr_scan_hook);
  prev_minor_begin_hook = atomic_exchange(&caml_minor_gc_begin_hook,
                                          record_minor_begin);
  prev_minor_end_hook = atomic_exchange(&caml_minor_gc_end_hook,
                                        record_minor_end);
  if (domain_termination != NULL) {
    domain_terminated_callback = domain_termination;
    prev_domain_terminated_hook = atomic_exchange(&caml_domain_terminated_hook,
                                                  domain_terminated_hook);
  }
}

#else

static void (*prev_scan_roots_hook)(scanning_action) = NULL;

static void bxr_scan_hook(scanning_action action)
{
  if (prev_scan_roots_hook != NULL) {
    (*prev_scan_roots_hook)(action);
  }
  int only_young = action == &caml_oldify_one;
  (*scanning_callback)(action, only_young, NULL);
}

_Thread_local bool bxr_thread_has_lock = false;

static void (*prev_enter_blocking)(void);
static void (*prev_leave_blocking)(void);

static void bxr_enter_blocking_section(void)
{
  bxr_thread_has_lock = false;
  prev_enter_blocking();
}

static void bxr_leave_blocking_section(void)
{
  prev_leave_blocking();
  bxr_thread_has_lock = true;
}

/* from <caml/signals.h> */
CAMLextern void (*caml_leave_blocking_section_hook)(void);
CAMLextern void (*caml_enter_blocking_section_hook)(void);

static void setup_thread_hooks()
{
  prev_leave_blocking = caml_leave_blocking_section_hook;
  prev_enter_blocking = caml_enter_blocking_section_hook;
  caml_leave_blocking_section_hook = bxr_leave_blocking_section;
  caml_enter_blocking_section_hook = bxr_enter_blocking_section;
  bxr_thread_has_lock = true;
}

bool bxr_check_thread_hooks()
{
  return caml_leave_blocking_section_hook == bxr_leave_blocking_section
    && caml_enter_blocking_section_hook == bxr_enter_blocking_section;
}

void bxr_setup_hooks(bxr_scanning_callback scanning,
                     caml_timing_hook domain_termination)
{
  scanning_callback = scanning;
  // save previous hooks
  prev_scan_roots_hook = caml_scan_roots_hook;
  prev_minor_begin_hook = caml_minor_gc_begin_hook;
  prev_minor_end_hook = caml_minor_gc_end_hook;
  // install our hooks
  caml_scan_roots_hook = bxr_scan_hook;
  caml_minor_gc_begin_hook = record_minor_begin;
  caml_minor_gc_end_hook = record_minor_end;
  setup_thread_hooks();
  (void)domain_termination;
}

/* caml_thread_initialize defined in
   ocaml/otherlibs/systhreads/st_stubs.c if systhreads is linked. */
#if defined(__GNUC__)
value caml_thread_initialize(value unit) __attribute__((weak));
/* We do nothing if systhreads is not linked */
value caml_thread_initialize(value) { return Val_unit; }
#else
value caml_thread_initialize(value unit);
#endif

void bxr_init_systhreads(void)
{
  caml_thread_initialize(Val_unit);
}

#endif // OCAML_MULTICORE

