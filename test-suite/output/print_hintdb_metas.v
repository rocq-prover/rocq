Theorem x : forall n m:nat, n = 1 /\ forall n : nat, n = m.
Proof.
Admitted.
Create HintDb foo.
Hint Resolve x : foo.
(* Note that the pattern doesn't have a metavariable for
  the inner forall n
  ie pattern is ?n = 1 /\ (forall n : nat, n = ?m) *)
Print HintDb foo.
