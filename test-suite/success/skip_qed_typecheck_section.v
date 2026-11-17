Set Skip Qed Typecheck.

(* Section variables used by an unchecked proof must still be declared. *)
Section S.
Variable x : nat.
Lemma foo : nat.
Proof using Type.
exact x.
Fail Qed.
Abort.
End S.
