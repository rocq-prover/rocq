Set Proof Using Clear Unused.

Section S.

  Variable x y : nat.

  Let z := x + x.

  Lemma foo : x + x = x + x.
  Proof using .
    Fail Check y.
    exact (eq_refl z).
  Defined.

  #[refine] Definition bar := x + _.
  Fail Proof using.
  Proof using x.
    Fail exact y.
    exact z.
  Defined.

  Lemma baz : bar = bar.
  Proof using y. (* x implicit through the type of the lemma *)
    Show.
    reflexivity.
  Defined.

  #[refine,using="y"] Definition baz' := bar + _.
  Fail Proof.
  Abort.

End S.
