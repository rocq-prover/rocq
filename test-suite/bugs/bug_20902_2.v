Lemma foo (P:unit -> Type) x (H:P x) : unit.
Proof.
  (* check that we pick the _rect eliminator because we generalize
  over H instead of picking the _rec eliminator by looking just at the goal *)
  induction x.
  exact tt.
Qed.
