Goal nat -> nat.
Proof.
  intros x .
  epose (_:>bool).
  (* questionable behaviour: unshelves a bool goal *)
  unshelve eapply plus in x.
  exact true.
  all: exact 0.
Qed.
