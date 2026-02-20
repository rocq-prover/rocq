Require Import Ltac2.Ltac2.

Axiom P : nat -> Prop.
Axiom p : forall n, P n.

Goal P 1 /\ P 2 /\ P 3 /\ P 4.
Proof.
  repeat split.
  Fail 1:exact (p 3). (* sanity check: "exact (p n)" assert that the goal was originally goal n *)
  all:Control.reorder_goals [1;3;4;2].
  4: exact (p 2).
  Fail all:Control.reorder_goals [1;2]. (* missing goal 3 *)
  Fail all:Control.reorder_goals [1;2;3;3]. (* duplicated goal 3 *)
  Fail all:Control.reorder_goals [1;4;3]. (* non existing goal 4 *)
  all:Control.reorder_goals [3;2;1];
    Control.dispatch [
        (fun () => exact (p 4));
        (fun () => exact (p 3));
        (fun () => exact (p 1))
      ].
Qed.
