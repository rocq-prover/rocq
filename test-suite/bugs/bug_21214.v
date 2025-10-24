Require Import Ltac2.Ltac2.

Module Cust.
  Ltac2 Custom Entry foo.
End Cust.
Module Nota.
  Import Cust.
  Ltac2 Notation "bar" c(foo) : foo(0) := c.
End Nota.
Import Nota.
(* error unknown entry foo *)

Ltac2 Notation "###" : Cust.foo(0) := ().
Ltac2 Notation "foo:(" c(Cust.foo) ")" := c.

Ltac2 Eval foo:(bar ###).
