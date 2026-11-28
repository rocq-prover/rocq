(* ../../nested/honest/Lib.v with X before Y. The forged copy of this
   library adds the alias A.X.d -> A.Y.d to the resolver of A, as in case
   nested, so the alias names A.Y.d, which is not yet in the environment
   when A.X is checked. *)

Unset Elimination Schemes.

Inductive bool : Set := true | false.

Inductive eq (A : Type) (x : A) : forall _ : A, Prop :=
| eq_refl : eq A x x.

Inductive False : Prop := .
Inductive True : Prop := I : True.

Definition discr (b : bool) : Prop :=
  match b with
  | true => True
  | false => False
  end.

Module A.
  Module X.
    Definition d : bool := false.
  End X.
  Module Y.
    Definition d : bool := true.
  End Y.
End A.

Module Type XT.
  Parameter d : bool.
End XT.

Module Type S.
  Declare Module X : XT.
End S.

Module F (P : S).
  Definition c' : bool := A.Y.d.
  Definition e : eq bool P.X.d P.X.d := eq_refl bool P.X.d.
End F.

Module Type T.
  Definition c' : bool := A.Y.d.
  Parameter e : eq bool A.X.d false.
End T.

Module R : T := F A.
