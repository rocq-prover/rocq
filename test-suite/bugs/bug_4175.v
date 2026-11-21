Require Import Setoid.

Axiom dummy : nat = bool.
Axiom foo : forall X, X + 0 = X.

Create HintDb rew.
Hint Rewrite foo dummy : rew.

Goal 1 + 0 = 1.
Proof.
rewrite_strat topdown (hints rew).
reflexivity.
Qed.

Goal 1 + 0 = 1.
Proof.
rewrite_strat bottomup (hints rew).
reflexivity.
Qed.

Goal 1 + 0 = 1.
Proof.
rewrite_strat outermost (hints rew).
reflexivity.
Qed.

Goal 1 + 0 = 1.
Proof.
rewrite_strat innermost (hints rew).
reflexivity.
Qed.

Goal (2 + 0) + 0 = 2.
Proof.
rewrite_strat repeat (outermost (hints rew)).
reflexivity.
Qed.

Definition T := nat.

Goal forall x : nat, @eq nat x x.
Proof.
intros x.
rewrite_strat subterm (fold T).
match goal with |- @eq T x x => idtac end.
reflexivity.
Qed.
