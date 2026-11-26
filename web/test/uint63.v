(* Primitive integers that do not fit 31 bits, computed by the kernel:
   under wasm_of_ocaml they go through Uint63_web (boxed Int64). *)
From Corelib Require Import PrimInt63.
Open Scope uint63_scope.

Definition big := Eval lazy in lsl 1 40.
Example e_big : big = 1099511627776 := eq_refl.
Example e_add : add big big = 2199023255552 := eq_refl.
Example e_mul : mul big 1024 = 1125899906842624 := eq_refl.
Example e_div : div big 4096 = 268435456 := eq_refl.
Example e_wrap : add (lsl 1 62) (lsl 1 62) = 0 := eq_refl.
Example e_max : sub 0 1 = 9223372036854775807 := eq_refl.
Example e_lt : ltb (lsl 1 62) (sub 0 1) = true := eq_refl.
Example e_cmp : compare big (add big 1) = Lt := eq_refl.
Example e_head0 : head0 big = 22 := eq_refl.
