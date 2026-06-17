exception SyntaxError of (Lexing.position * Lexing.position) * string

type sexp =
  (Lexing.position * Lexing.position) * rawsexp
and rawsexp =
| Atom of string
| Var of string
| String of string
| List of sexp list

val read_next_sexp : Lexing.lexbuf -> sexp
val read_only_sexp : Lexing.lexbuf -> sexp

val print : Format.formatter -> sexp -> unit
