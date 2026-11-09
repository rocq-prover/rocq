Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS : forall n: nat, ev n -> ev (S (S n)).

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros H. inversion H as [| _ [| n' H']].
  inversion H'.
Qed.
