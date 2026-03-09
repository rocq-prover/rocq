(* Regression test for bug #21730 *)
(* Scheme Elimination for an included inductive should not cause a universe anomaly *)

Definition binary (A : Type) := A -> A -> Prop.

Module Export SLF_DOT_LibContainer_WRAPPED.
Module Export LibContainer.
Class BagDisjoint T := { disjoint : binary T }.
End LibContainer.

Module Export SLF.
Module Export LibContainer.
Include SLF_DOT_LibContainer_WRAPPED.LibContainer.
Scheme SLF_LibContainer_BagDisjoint_caset := Elimination for SLF.LibContainer.BagDisjoint Sort Type.
End LibContainer.
End SLF.
End SLF_DOT_LibContainer_WRAPPED.
