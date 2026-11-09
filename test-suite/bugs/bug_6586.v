From Corelib Require Import Setoid.

Axiom Z : Type.
Axiom zmul : Z -> Z -> Z.
Axiom foo : forall {G} (R : G -> G -> Prop) (mul : Z -> G -> G) (n : Z) (P : G), R (mul n P) P.

Goal forall (R : Z -> Z -> Prop) `{Reflexive _ R} `{Transitive _ R} (n : Z), R (zmul n n) n.
Proof.
  intros R ? ? n.
  rewrite @foo with (mul := zmul) (G := Z).
  reflexivity.
Qed.

Axiom bar : forall (A : Type) (R : A -> A -> Prop) (x : A), R x x.

Goal forall (R : nat -> nat -> Prop), R 0 0.
Proof.
  intros R.
  Fail rewrite bar with (x := 0) (A := bool).
Abort.

Axiom baz : forall (A : Type) (R : A -> Prop) (x : A), R x.

Goal forall (R : nat -> Prop), R 0.
Proof.
  intros R.
  Fail rewrite baz with (x := 0) (A := nat).
Abort.
