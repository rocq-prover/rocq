(* The universes of fresh instances which only bound the types of the arguments of a fully
   applied global are set to their lower bound, even without Universe Minimization ToSet *)
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Unset Universe Minimization ToSet.
Set Printing Universes.

Inductive sig' (A : Type) (P : A -> Type) := ex' (x : A) (p : P x).
Inductive eq' (A : Type) (x : A) : A -> Type := refl' : eq' A x x.

(* The universes bounding nat in sig' and ex' are Set: shift only quantifies over P's *)
Definition shift (P : nat -> Type) (f : forall n, P n -> P (S n)) (x : sig' nat P) : sig' nat P :=
  match x with ex' _ _ n a => ex' nat P (S n) (f n a) end.
About shift.

Definition refl_S (n : nat) := refl' nat (S n).
About refl_S.

(* A parameter solved after the application: its universe is raised by the argument *)
Definition with_hole (B : Type) (b : B) : sig' B (fun _ => B) := ex' _ _ b b.
About with_hole.

(* The universe of the parameter becomes the one of the binder B, whose type is solved by the
   occurrence: it is not irrelevant anymore and must not be set to Set *)
Definition crel (A : Type) := A -> A -> Type.
Definition use_crel {B} (R : crel B) : crel B := R.
About use_crel.
