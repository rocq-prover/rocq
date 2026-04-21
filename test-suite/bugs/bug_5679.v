Goal False -> True.
Proof.
  intros H.
  Fail elim H using nat. (** Anomaly "last_arg." Please report at http://coq.inria.fr/bugs/. *)
  Fail elim H using True_ind.
  Fail elim H using 0.
  Fail induction H using nat.
  Fail induction H using True_ind.
  Fail induction H using 0.
  elim H using False_ind.
Qed.
