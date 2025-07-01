Theorem x : forall n m:nat, n = 1 /\ forall n : nat, n = m.
Admitted.
Hint Resolve x : foo.
Print HintDb foo.
(* Note that the pattern doesn't have a metavariable for
  the inner forall n
  ie pattern is ?n = 1 /\ (forall n : nat, n = ?m) *)
