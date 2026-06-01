
Axiom t : Type -> Type.

Section S.
  Variable elt : Type.

  Lemma t_ind :
   forall P : t elt -> Type,
   forall m, P m.
  Proof.
  Admitted.

  Goal forall m : t elt, m = m.
    induction m using t_ind.
  Qed.
End S.
