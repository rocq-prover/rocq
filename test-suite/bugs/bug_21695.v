Module Type T. Parameter n : bool. End T.
Module M_true.  Definition n := true.  End M_true.
Module M_false. Definition n := false. End M_false.

Module A. Module B. Module F (E : T).
  Module Inner. Definition x := E.n. End Inner.
  Module Alias := Inner.
End F. End B. End A.

Module A' := A.
Module B' := A'.B.
Module R  := B'.F M_true.
Module R' := B'.F M_false.

Fail Check (eq_refl : R.Alias.x = R'.Alias.x).

(*
Lemma boom : False.
Proof.
  assert (H : R.Alias.x = R'.Alias.x) by reflexivity.
  lazy in H. discriminate H.
Qed.
*)
