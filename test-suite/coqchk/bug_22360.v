(* -*- coqchk-prog-args: ("-bytecode-compiler" "yes") -*- *)

Require Import PrimString.

Open Scope pstring_scope.

(* The VM data validator capped caml_prim at its 6 array primitives, so the
   bytecode of any string primitive failed to intern. A string literal alone
   does not exercise this; the primitives have to be applied. *)
Definition greeting := PrimString.cat "hello, " "world".
Definition len := PrimString.length greeting.
Definition cmp := PrimString.compare greeting "".
