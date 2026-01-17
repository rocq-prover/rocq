Set Universe Polymorphism.

Definition relation@{s;u|} (A : Univ@{s;u}) := A -> Set.
Axiom fail@{a s;a u|+} : forall {A : Univ@{s;u}}, relation@{s;u} (A -> A).

Arguments fail {A}%_type _.

About fail.
