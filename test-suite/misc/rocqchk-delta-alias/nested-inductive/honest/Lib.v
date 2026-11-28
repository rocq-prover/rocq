(* The forged copy of this library adds the alias A.X.I -> A.Y.I to the
   resolver of A, not to that of A.X, and makes T and R state
   e : forall _ : A.Y.I, False. A.Y.I has a constructor and A.X.I has none.
   c' names A.Y.I for forge.ml. *)

Unset Elimination Schemes.

Inductive False : Prop := .

Module A.
  Module Y.
    Inductive I : Prop := i : I.
  End Y.
  Module X.
    Inductive I : Prop := .
  End X.
End A.

Module Type XT.
  Inductive I : Prop := .
End XT.

Module Type S.
  Declare Module X : XT.
End S.

Module F (P : S).
  Definition c' : Prop := A.Y.I.
  Definition e : forall _ : P.X.I, False :=
    fun x => match x return False with end.
End F.

Module Type T.
  Definition c' : Prop := A.Y.I.
  Parameter e : forall _ : A.X.I, False.
End T.

Module R : T := F A.
