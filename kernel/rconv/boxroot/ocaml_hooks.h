/* SPDX-License-Identifier: MIT */
#ifndef OCAML_HOOKS_H
#define OCAML_HOOKS_H

#ifndef __cplusplus
#include <stdbool.h>
#endif

#include "platform.h"

#ifdef __cplusplus
extern "C" {
#define _Thread_local thread_local
#endif

#if OCAML_MULTICORE

#define bxr_domain_lock_held() (BXR_LIKELY(Caml_state_opt != NULL))

#else

/* true when the master lock is held, false otherwise */
extern _Thread_local bool bxr_thread_has_lock;

/* We need a way to detect concurrent mutations of
   [caml_enter/leave_blocking_section_hook]. They are only overwritten
   once at systhreads init (we assume that no piece of code in the
   OCaml ecosystem is as insane as the present one). If we see this
   happening, we place boxroot in safety mode (all allocations fail). */
#define bxr_domain_lock_held() (BXR_LIKELY(bxr_thread_has_lock))

#endif // OCAML_MULTICORE

#ifdef __cplusplus
} // extern "C"
#endif

#ifdef CAML_INTERNALS

#include <caml/mlvalues.h>
#include <caml/roots.h>
#include <caml/signals.h>
#include <caml/version.h>

typedef struct {
  uintnat start;
  uintnat range;
} minor_heap_info;

/* Fast range check for efficient young classification.

   Optimise for branch prediction: if v falls within the young range,
   then it is likely that it is a block. */
#define Bxr_is_young(info, v)                                           \
  ((uintnat)(v) - (info).start <= (info).range && BXR_LIKELY(Is_block(v)))

#if OCAML_MULTICORE

#define CALL_GC_ACTION(action, data, v, p) action(data, v, p)
#define Add_to_ref_table(dom_st, p)                   \
  Ref_table_add(&dom_st->minor_tables->major_ref, p);

static inline minor_heap_info get_minor_heap_info(void)
{
  /* If a <= b - 2 then
     a < x && x < b  <=>  x - a - 1 <= b - a - 2 (unsigned comparison)
  */
  return (minor_heap_info) {
    .start = (uintnat)caml_minor_heaps_start + 1,
    .range = (uintnat)caml_minor_heaps_end - (uintnat)caml_minor_heaps_start - 2
  };
}

#else

#define CALL_GC_ACTION(action, data, v, p) do {       \
    action(v, p);                                     \
    (void)data;                                       \
  } while (0)
#define Add_to_ref_table(dom_st, p) add_to_ref_table(dom_st->ref_table, p)

static inline minor_heap_info get_minor_heap_info()
{
  return (minor_heap_info) {
    .start = (uintnat)Caml_state->young_start,
    .range = (uintnat)Caml_state->young_end - (uintnat)Caml_state->young_start
  };
}

#endif // OCAML_MULTICORE

typedef void (*bxr_scanning_callback) (scanning_action action,
                                       int only_young, void *data);

/* Must be called while holding the domain lock */
void bxr_setup_hooks(bxr_scanning_callback scanning,
                     caml_timing_hook domain_termination);

bool bxr_in_minor_collection();

#if !OCAML_MULTICORE

void bxr_init_systhreads();

/* Used to regularly check that the hooks have not been overwritten.
   If they have, we place boxroot in safety mode. */
bool bxr_check_thread_hooks();

#endif // !OCAML_MULTICORE

#endif // CAML_INTERNALS

#endif // OCAML_HOOKS_H
