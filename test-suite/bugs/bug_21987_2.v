Goal True /\ True -> True.
Proof.
  intros H.
  match goal with
  | H : _ /\ _ |- _ =>
     destruct H as [H1 H2]; try clear H
  end.
Abort.
