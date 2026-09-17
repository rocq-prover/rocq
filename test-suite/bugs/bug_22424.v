Set Primitive Projections.
Module Type T. Record    R : Set := mk { p1 : nat }. End T.  (* BiFinite -> eta   *)
Module M.      Inductive R : Set := mk { p1 : nat }. End M.  (* Finite   -> NoEta *)
Module F (X : T).
  Definition eta (x : X.R) : x = X.mk (X.p1 x) := eq_refl.
End F.
Fail Module G := F M.

(* Variant from #15842 *)

Module Type S.

  Unset Elimination Schemes.

  Inductive Bla := .

End S.

Module N.
Variant Bla := .
End N.

Module G(X:S).
  #[warning="-non-recursive"]
  Fixpoint go (x:X.Bla) : False := match x with end.
End G.

Fail Module Bad := F M.
