(* Rewriting with a rule with a hole under a binder whose type is an evar
   defined during the interpretation of the rule: the evar for the hole has a
   context larger than the goal's, which mentions this defined evar. This is
   the shape of a proof of mathcomp's algebra/poly.v. *)

Require Import ssreflect.

Definition apply {A B : Type} (f : A -> B) (a : A) := f a.
Lemma applyE {A B : Type} (f : A -> B) (a : A) : apply f a = f a.
Proof. by []. Qed.

Lemma rw_hole_under_binder : apply (fun y : nat => S y) 0 = 1.
Proof. by rewrite (applyE (fun (y : id _) => _)). Qed.

Lemma rw_multi_hole_under_binder :
  apply (fun y : nat => S y) 0 + apply (fun n : nat => n) 1 = 1 + 1.
Proof. by rewrite !(applyE (fun (y : id _) => _), applyE). Qed.

Set Universe Polymorphism.

Definition papply@{u v} {A : Type@{u}} {B : Type@{v}} (f : A -> B) (a : A) := f a.
Lemma papplyE@{u v} {A : Type@{u}} {B : Type@{v}} (f : A -> B) (a : A) :
  papply f a = f a.
Proof. by []. Qed.

Lemma rw_poly_hole_under_binder (A : Type) (a : A) (g : A -> A) :
  papply (fun y : A => g y) a = g a.
Proof. by rewrite (papplyE (fun (y : id _) => _)). Qed.
