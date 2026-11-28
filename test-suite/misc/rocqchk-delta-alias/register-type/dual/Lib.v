(* The forged copy registers the parameter int as the int63 type, with the
   canonical name of N.int, which is Empty_set. *)

Unset Elimination Schemes.

Inductive False : Prop := .
Inductive Empty_set : Set := .

Module N.
  Definition int : Set := Empty_set.
End N.

Parameter int : Set.

(* A declaration that names N.int and int, for forge.ml. *)
Definition from_N : forall (_ : N.int), int := fun x => match x return int with end.
