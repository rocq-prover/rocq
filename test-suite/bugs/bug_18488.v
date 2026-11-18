From Corelib Require Import ssreflect.

Goal True -> True.
Proof.
move=> H. apply: (H) {H}.
Qed.

Goal forall P : Prop, P -> P /\ True.
Proof.
move=> P H; apply: conj (H) _ {H}.
Fail exact H.
exact I.
Qed.

Goal True -> True.
Proof.
move=> H. exact: (H) {H}.
Qed.
