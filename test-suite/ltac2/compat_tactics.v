From Ltac2 Require Import Ltac2 Ltac1CompatNotations.

(* rename *)
Goal forall (x : nat), x = x.
Proof.
  intro x.
  rename x into y.
  exact (@eq_refl _ y).
Qed.
