Module Type T.
  Parameter T : Type.
End T.

Module F(A:T).
  Inductive X : A.T -> Prop := .
End F.

Module A.
  Definition T := True.
End A.

Module M := F A.
