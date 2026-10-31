From Corelib Require Import Program.Tactics.

Definition anyp (A : Type) : Type := unit.

Axiom (H : forall (A : Type), (anyp A) -> False).

Program Definition main (A : Type) : False := H A _.

Definition anyp_eq {A} : anyp A = unit := eq_refl.

Next Obligation.
  rewrite anyp_eq.
  exact tt.
Qed. (* Anomaly "in Univ.repr: Universe Test.60 undefined." *)
