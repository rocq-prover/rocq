Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

#[universes(template)] Inductive foo (A : Type) := C (a : A).
Check foo nat : Set.
Fail Check foo@{Set}.

#[universes(template)] Record bar (A : Type) := { x : A }.
Check bar nat : Set.
Fail Check bar@{Set}.

Fail #[universes(template), universes(polymorphic)] Inductive qux (A : Type) := E (a : A).
