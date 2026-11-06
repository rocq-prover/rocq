(* With Skip Qed Typecheck, Qed does not run the kernel's typechecking of the
   proof, which here would compute 2^22 boolean negations. *)
(* Expected time < 0.50s *)

Set Skip Qed Typecheck.

Fixpoint pow2 (n : nat) (b : bool) : bool :=
  match n with O => negb b | S n => pow2 n (pow2 n b) end.

Lemma big : pow2 22 true = true.
Proof.
exact_no_check (eq_refl true).
Time Qed.
