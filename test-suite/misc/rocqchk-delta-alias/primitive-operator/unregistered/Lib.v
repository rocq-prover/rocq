(* No primitive type is registered. The forged copy gives the axiom bogus
   the body #int63_head0, whose type, int -> int, names the int63 type. *)

Unset Elimination Schemes.

Inductive False : Prop := .

Axiom bogus : False.
