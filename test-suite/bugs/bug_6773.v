Section BuggySection.

  Variable B: nat.

  Axiom F: False. (* To replace admits, allowing QED in bug*)

  Lemma BUG (i: nat) : False.
  Proof.
    induction i in B.
    assert (B = B) by abstract reflexivity.
    all: now destruct F. (* No more subgoals. *)
  Qed. (* fails *)

End BuggySection.
