Set Universe Polymorphism.
Set Primitive Projections.
Set Polymorphic Inductive Cumulativity.
Unset Collapse Sorts ToType.
Record id {A} (x : A) : Prop := {}.
Axiom foo1 : id I.
Axiom foo2 : id@{Prop;_} I.

Check eq foo1 foo2.
(* File "./test.v", line 8, characters 14-18:
Error:
The term "foo2" has type "id@{Prop ; test.26} I"
while it is expected to have type "id@{Type ; Set} I"
(universe inconsistency: Cannot enforce Prop = Set). *)
