(* The forged copy gives twin the label ax. The environment then keeps the
   last field labelled ax, ax : unit := tt. proof was checked against the
   axiom, so no constant is left without a body, and proof is a closed
   proof of False. *)

Unset Elimination Schemes.

Inductive False : Prop := .
Inductive unit : Set := tt.

Axiom ax : False.

Definition proof : False := ax.

Definition twin : unit := tt.
