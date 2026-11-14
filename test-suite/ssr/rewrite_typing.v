From Corelib Require Import ssreflect.

Axiom f : nat -> nat.
Axiom L : f 0 = 1.

Goal (fun n : nat => f (fst (0, n))) = (fun _ => 1).
Proof.
Fail rw L.
Fail rw [f _]L.
Abort.

Lemma closed_redex_from_pattern :
  (fun n : nat => f (fst (0, n)) + 0) = (fun _ => 1 + 0).
Proof.
rw [f _ as X in fun n => X + _]L.
reflexivity.
Qed.

Axiom D : nat -> Prop.
Axiom d : forall n, D n.

Goal exist D (f 0) (d (f 0)) = exist D (f 0) (d (f 0)).
Proof.
Fail rw {1}L.
rw L.
reflexivity.
Qed.

Universes u v.
Constraint u < v.
Axiom X Y : Type@{u}.
Axiom P : Type@{u} -> Prop.
Axiom E : @eq Type@{v} X Y.

Goal P X.
Proof.
Fail rw E.
Abort.

Lemma motive_universe_flex (E' : @eq Type X Y) : P Y -> P X.
Proof.
intros H.
rw E'.
exact H.
Qed.

Axiom Q : Type@{v} -> Prop.

Lemma motive_universe_flex_up (E' : @eq Type X Y) : Q Y -> Q X.
Proof.
intros H.
rw E'.
exact H.
Qed.
