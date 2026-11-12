Goal forall n m, n + m = m + n.
Proof.
  intros.
  Fail destruct n, m using nat_ind.
  Fail induction n, m using nat_ind.
  Fail destruct n using (nat_case _).
Abort.
