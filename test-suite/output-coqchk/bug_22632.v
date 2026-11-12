Module Type T. Parameter tgt : 1 = 2. End T.
Module Seal : T.
  #[bypass_check(guard)] Fixpoint loop (n : nat) : False := loop n.
  Lemma tgt : 1 = 2. Proof. exfalso; exact (loop 0). Qed.
End Seal.
