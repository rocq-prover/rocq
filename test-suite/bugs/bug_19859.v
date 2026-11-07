Require Import ssreflect.

Axiom A : Type.
Axiom B : A -> Type.

Goal False.
Proof.
  pose f' (a : A) (_ := true) := _.
  pose g (a : A) (b := a) (c : B b) := (_ : B b).
  pose k (n : nat) (m := S n) := (_ : m = m).
Abort.
