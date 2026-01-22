#include <stdlib.h>
#include <stdio.h>
#include <caml/memory.h>
#include <memory.h>

/* Keep in sync with rocq_values.c */

#if defined(__GNUC__) && defined(__amd64__)

#define rocq_proxy_accu_defined

#elif defined(__GNUC__) && defined(__i386__)

#define rocq_proxy_accu_defined

#endif

value rocq_native_5x_available(value dummy) {
#ifdef rocq_proxy_accu_defined
  return Val_int(1);
#else
  return Val_int(0);
#endif
}
