Section Test.
 Context (H : True).
 Goal True /\ True -> True.
 Proof.
   intros H'. rename H into H0. rename H' into H.
   repeat match goal with [ H : _ /\ _ |- _ ] => destruct H end. (* fails with timeout because [H] is not cleared by [destruct] *)
   trivial.
 Qed.
End Test.
