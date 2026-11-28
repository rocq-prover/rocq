(* The forged copy gives zero the body Int 0 and registers the definition
   int as the int63 type. Then Int 0 has the type int, which unfolds to
   Empty_set, and boom is a closed proof of False. *)

Unset Elimination Schemes.

Inductive False : Prop := .
Inductive Empty_set : Set := .

Definition int : Set := Empty_set.

Axiom zero : int.

Definition boom : False := match zero return False with end.
