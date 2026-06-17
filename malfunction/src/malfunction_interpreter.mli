open Malfunction

exception Error of string

type value =
| Block of int * value array
| Vec of vector_type * value array
| Func of (value -> value)
| Int of inttype * Z.t
| Float of float
| Thunk of value Lazy.t

val eval : t -> value
val render_value : value -> Malfunction_sexp.sexp
