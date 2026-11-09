Definition foo (A : Type) (x : A) : nat -> A.
Proof.
refine (fix f (n : nat) : A := _).
exact_no_check n.
Fail Validate Proof.
Fail Defined.
Abort.
