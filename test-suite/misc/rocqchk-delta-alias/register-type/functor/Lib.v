(* R := F N, and F's M : T := P, so the only declaration of R.M.int is the
   parameter of T, in R's type; N.int is Empty_set. The forged copy
   registers R.M.int as the int63 type. *)

Unset Elimination Schemes.

Inductive False : Prop := .
Inductive Empty_set : Set := .

Module Type T.
  Parameter int : Set.
  Parameter int_empty : forall (_ : int), False.
End T.

Module N : T.
  Definition int : Set := Empty_set.
  Definition int_empty : forall (_ : int), False :=
    fun x => match x return False with end.
End N.

Module F (P : T).
  Module M : T := P.
End F.

Module R := F N.

(* A declaration that names R.M.int, for forge.ml. *)
Definition uses : Set := R.M.int.
