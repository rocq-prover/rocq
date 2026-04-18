From Corelib Require Import Setoid.
Definition silly (n : nat) := True.
Ltac silly :=
  lazymatch goal with
  | [ |- silly 1 ] => constructor
  end.
Axiom sillyL : forall x, silly x -> x = 0 + 0.
Hint Rewrite sillyL using solve [ silly ] : silly.
Goal 1 + 0 = 0.
Proof.
  progress autorewrite* with silly.
  reflexivity.
Qed.
Goal 1 + 0 = 0.
Proof.
  rewrite* sillyL by silly.
  reflexivity.
Qed.
