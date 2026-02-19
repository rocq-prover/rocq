Set Generate Goal Names.

Goal forall a b c : bool, True.
Proof.
  intros.
  destruct a.
  [true]: {
    refine _.
    destruct b, c.
    all: exact I.
  }
  [false]: exact I.
Qed.
