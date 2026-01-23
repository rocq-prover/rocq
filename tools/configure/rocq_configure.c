#include <caml/memory.h>

/* Keep in sync with rocq_values.c */

#if defined(__GNUC__) && defined(__amd64__)
#elif defined(__GNUC__) && defined(__i386__)
#elif defined(NO_NAKED_POINTERS)
#define no_native_compute
#endif

value rocq_native_available(value dummy) {
#ifdef no_native_compute
  return Val_int(0);
#else
  return Val_int(1);
#endif
}
