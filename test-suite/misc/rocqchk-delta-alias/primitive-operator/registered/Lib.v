(* The operators are declared as coqc declares them: add in the sealed
   module MI, whose type IT declares it as a parameter; after MI, eqb, whose
   type names MI's int and the inductive type bool that this library
   registers; and make, whose universe instance has length one. The forged
   copy gives the axiom bogus the body #int63_head0, whose type is
   int -> int, not False. *)

Unset Elimination Schemes.

Inductive False : Prop := .

Module Type IT.
  Parameter int : Set.
  Parameter add : forall (_ : int) (_ : int), int.
End IT.

Module MI : IT.
  Primitive int := #int63_type.
  Primitive add := #int63_add.
End MI.

Inductive bool : Set := true | false.
Register bool as kernel.ind_bool.

Primitive eqb := #int63_eq.

Primitive array := #array_type.
Primitive make := #array_make.

Axiom bogus : False.
