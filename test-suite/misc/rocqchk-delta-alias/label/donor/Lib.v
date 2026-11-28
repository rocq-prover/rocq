(* ../honest/Lib.v, except that F's lemma is an axiom that says
   A.X.k = false, as F A's does with the forged library. *)

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
    Definition k : bool := true.
    Definition f : eq bool d false := eq_refl bool false.
  End X.
End A.

Module Type XS.
  Parameter d : bool.
  Parameter f : eq bool d false.
End XS.

Module Type S.
  Declare Module X : XS.
End S.

Module F (P : S).
  Definition k : bool := P.X.d.
  Axiom lemma : eq bool A.X.k false.
End F.
