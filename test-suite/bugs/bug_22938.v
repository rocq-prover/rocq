From Corelib Require Import PrimFloat FloatClass.

Open Scope float_scope.

Inductive Wrap : Set := wrap : float -> Wrap.

(* Native symbol deduplication used OCaml (=), which equates +0.0 and -0.0,
   collapsing wrap 0 and wrap (-0) into the same symbol table entry. *)
Fail Definition bad : wrap 0 = wrap (-0) :=
  eq_refl (wrap 0) <<: wrap 0 = wrap (-0).

Definition unw (w : Wrap) : float :=
  match w with wrap x => x end.

Definition good_pzero : PrimFloat.classify (unw (wrap 0)) = PZero :=
  eq_refl PZero <<: PrimFloat.classify (unw (wrap 0)) = PZero.

Definition good_nzero : PrimFloat.classify (unw (wrap (-0))) = NZero :=
  eq_refl NZero <<: PrimFloat.classify (unw (wrap (-0))) = NZero.
