(* The forged copy of this library makes M2.c an alias of M1.c. Both are
   declared-only in the type of their module, and the alias keeps its label,
   as the aliases coqc writes do. *)

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
  Parameter f : eq bool c false.
End TF.

Module M2 : TF.
  Definition c : bool := false.
  Definition f : eq bool c false := eq_refl bool false.
End M2.
