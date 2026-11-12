(* ../honest/Lib.v, except that f says M1.c = false, which the forged library
   makes it say. *)

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

Module Type TT.
  Parameter c : bool.
  Parameter e : eq bool true c.
End TT.

Module M1 : TT.
  Definition c : bool := true.
  Definition e : eq bool true c := eq_refl bool true.
End M1.

Module Type TF.
  Parameter c : bool.
  Parameter f : eq bool M1.c false.
End TF.

Module M2 : TF.
  Definition c : bool := false.
  Parameter f : eq bool M1.c false.
End M2.
