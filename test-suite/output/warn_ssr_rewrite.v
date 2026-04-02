Require Import ssreflect.

(* warns *)
Ltac foo H := rewrite H.

Goal forall x, x = x + 1 -> x = x + 2.
Proof.
  intros x H.
  (* doesn't warn *)
  foo H.
  (* warns *)
  rewrite H.
Abort.
