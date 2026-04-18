Theorem a : nat.
Proof.
apply O.
Qed.

Theorem b : a <> a.
Proof.
Fail unfold a at 2.
Abort.
