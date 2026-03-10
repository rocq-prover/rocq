Set Universe Polymorphism.

Module Irrel.
Polymorphic Record foo@{s;u|} (x : Type@{s;u}) := {}.

Module Type A. Axiom A@{i} : Type@{i}. Axiom B : foo A. End A.
Module B <: A. Axiom A@{i} : Prop. Axiom B : foo A. End B.
End Irrel.


Module NotIrrel.
#[universes(polymorphic,cumulative=no)] Record foo@{s;u|} (x : Type@{s;u}) := { }.

Unset Polymorphic Assumptions Cumulativity.

Module Type A. Axiom A@{i} : Type@{i}. Axiom B : foo A. End A.
Module B <: A. Axiom A@{i} : Prop. Axiom B : foo A. Fail End B.
