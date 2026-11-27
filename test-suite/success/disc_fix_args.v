(* A fixpoint reached by looking through a transparent head may still
   reduce, so dnets must not index it as a rigid term. *)

Inductive tm := Var (n : nat) | Fold (t : tm) | Unfold (t : tm).

Class Subst := subst : (nat -> tm) -> tm -> tm.

Class Red (t u : tm) := red : True.
#[export] Instance red_unfold t : Red (Unfold (Fold t)) t := I.

Goal Red (@subst (fix sub (s : nat -> tm) (t : tm) {struct t} : tm :=
    match t with Var n => s n | Fold t => Fold (sub s t) | Unfold t => Unfold (sub s t) end)
  (fun _ => Fold (Var 0)) (Unfold (Var 1))) (Var 0).
Proof. exact _. Qed.
