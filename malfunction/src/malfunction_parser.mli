open Malfunction

type moduleexp =
| Mmod of binding list * t list

(* Read the next expression from a lexbuf *)
val read_expression : Lexing.lexbuf -> t

val parse_expression : Malfunction_sexp.sexp -> t

(* Read an entire module from a lexbuf (must be followed by EOF) *)
val read_module : Lexing.lexbuf -> moduleexp
