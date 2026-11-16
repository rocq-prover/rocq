From Corelib Require Import Setoid.

Goal forall (P : nat -> Prop) (H : P 0), True.
Proof.
  intros.
  evar (R' : nat -> Prop).
  assert (H' : forall x, P x <-> R' x) by admit.
  rewrite H' in H.
Abort.
