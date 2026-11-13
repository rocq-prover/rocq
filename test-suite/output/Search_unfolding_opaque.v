Module M.
Definition double : forall n : nat, nat.
Proof.
  intros n.
  induction n as [ | n' IHn'].
  - exact O.
  - exact (S (S IHn')).
Defined.

Lemma n_le_double : forall n, n <= double n.
Proof. Admitted.

Definition opaque_double : forall n : nat, nat.
Proof.
  intros n.
  induction n as [ | n' IHn'].
  - exact O.
  - exact (S (S IHn')).
Qed.

Lemma n_le_opaque_double : forall n, n <= opaque_double n.
Proof. Admitted.

Search (S(S _)) in M.
Set Search Mod Unfolding.
Search (S(S _)) in M. (* New: n_le_double *)
End M.
