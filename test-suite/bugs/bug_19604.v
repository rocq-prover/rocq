Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

#[universes(template)] Inductive foo (A : Type) := C (a : A).
Check foo nat : Set.
Fail Check foo@{Set}.

#[universes(template)] Record bar (A : Type) := { x : A }.
Check bar nat : Set.
Fail Check bar@{Set}.

(* Template polymorphism is supported in universe polymorphic mode: the inductive is template
   polymorphic, its derived eliminators universe polymorphic *)
#[universes(template), universes(polymorphic)] Inductive qux (A : Type) := E (a : A).
Check qux nat : Set.
