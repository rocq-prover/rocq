Section S.
Variable x : nat.
Lemma a : x = x.
Proof using x. reflexivity. Qed.
Lemma b : True.
Proof using. exact I. Qed.
End S.
