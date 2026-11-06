Module M.
Definition one := 1.
Definition also_one := 1.

Theorem H : (1 + 1) = 2. Proof. reflexivity. Qed.
Theorem I : (1 + one) = 2. Proof. reflexivity. Qed.
Theorem J : (one + 1) = 2. Proof. reflexivity. Qed.
Theorem K : (one + one) = 2. Proof. reflexivity. Qed.
Theorem L : (one + also_one) = 2. Proof. reflexivity. Qed.

Search (?x + ?x) in M.
Set Search Mod Unfolding.
Search (?x + ?x) in M. (* New: I J L *)
End M.
