Require Import ssreflect.

Section Injections.

Variables (rT aT : Type) (f : aT -> rT).

Definition cancel g := forall x, g (f x) = x.

Definition pcancel g := forall x, g (f x) = Some x.

Succeed Constraint eq.u0 < Injections.u1.

Lemma can_pcan g : cancel g -> pcancel (fun y => Some (g y)).
Proof. by move=> fK x; congr (Some _). Defined.

Constraint eq.u0 < Injections.u1.
Fail Constraint Injections.u1 < eq.u0.

End Injections.
