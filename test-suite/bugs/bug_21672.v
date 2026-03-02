Require Import Corelib.Array.PrimArray.
Axiom P : forall A t i (a:A), get t i = a.
Axiom Q : forall A a i, @length@{length.u0} A a = i.
Lemma test : forall A a i, @length@{P.u0} A a = i.
Proof.
  intros A a i.
  Succeed refine (Q _ _ _).
Abort.
