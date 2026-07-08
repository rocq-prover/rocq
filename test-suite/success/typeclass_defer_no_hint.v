(* A typeclass goal with no applicable hint may still be solved as a side
   effect of resolving the remaining goals: below, [?a : A] has no instance,
   but resolving [?b : B ?a] with [b0 : B a0] instantiates [?a := a0].
   The resolution fixpoint must defer the failed goal and retry it after
   progress instead of failing eagerly (regression in the fix for #21044,
   which broke fiat-crypto's Bedrock/End2End/X25519/MontgomeryLadder.v:
   the [FieldParameters] instance is only reachable through unification
   against the [FieldRepresentation] instance). *)
Class A : Type := {}.
Class B (a : A) : Type := {}.
Axiom a0 : A.
Axiom b0 : B a0.
#[local] Existing Instance b0.
Definition body {a : A} {b : @B a} : nat := 0.
Definition foo := body.

(* Same, with a successfully resolvable goal in front. *)
Class W : Type := {}.
#[global] Instance w0 : W := {}.
Definition body' {w : W} {a : A} {b : @B a} : nat := 0.
Definition foo' := body'.
