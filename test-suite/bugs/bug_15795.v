Lemma bla : True * Type.
Proof.
  assert (H:Type@{_}) by admit.
  let t' := constr:(Type) in let t := type of H in unify t' t.
  (* type of H is typ@{u}, ustate has {u u'} |= u = u', u := u' (with u' rigid) *)

  split.
  1: abstract exact I.
  (* abstract ran UState.minimize so ustate has {u'} |=, u := u'
     update_sigma_univs then drops u from the ustate's ugraph *)

  Fail match goal with H : ?t |- ?t => idtac end.
  (* conversion uses the ustate's ugraph to check universes without normalizing them, so dies *)

Admitted.
