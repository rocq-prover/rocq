Require Import Ltac2.Ltac2.

Goal forall n: nat, True /\ n = n.
Proof.
  intros.
  split.
  all: revgoals.
  - exact eq_refl.
  - exact I.
Qed.
