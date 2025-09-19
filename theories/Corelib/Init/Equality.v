(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export Notations.
Require Import Ltac.

Notation "A -> B" := (forall (_ : A), B) : type_scope.

Create HintDb typeclass_instances discriminated.

Set Universe Polymorphism.

Section J_as_a_class.

  Class Has_refl@{sa se;la le} (eq : forall A : Type@{sa;la}, A -> A -> Type@{se;le})
  := refl : forall A x, eq A x x.

Arguments refl {_ _}.

Register Has_refl as rocq.core.Has_refl.

Class Has_J@{sa se sp;la le lp} (eq : forall A : Type@{sa ; la}, A -> A -> Type@{se;le})
  (Has_refl : Has_refl eq) :=
  J : forall (A : Type@{sa ; la}) (x : A) (P : forall y : A, eq A x y -> Type@{sp ; lp}),
    P x (refl A x) -> forall y e, P y e.

Class Has_J_forward@{sa se sp;la le lp} (eq : forall A : Type@{sa ; la}, A -> A -> Type@{se;le})
  (Has_refl : Has_refl eq) :=
  J_forward : forall (A : Type@{sa ; la}) (x : A) (P : forall y : A, eq A x y -> Type@{sp ; lp}) y e,
      P y e -> P x (refl A x).

Class Has_J_r@{sa se sp;la le lp} (eq : forall A : Type@{sa ; la}, A -> A -> Type@{se;le})
  (Has_refl : Has_refl eq) :=
  J_r : forall (A : Type@{sa ; la}) (x : A) (P : forall y : A, eq A y x -> Type@{sp ; lp}),
    P x (refl A x) -> forall y e, P y e.

Class Has_J_r_forward@{sa se sp;la le lp} (eq : forall A : Type@{sa ; la}, A -> A -> Type@{se;le})
  (Has_refl : Has_refl eq) :=
  J_r_forward : forall (A : Type@{sa ; la}) (x : A) (P : forall y : A, eq A y x -> Type@{sp ; lp}) y e,
      P y e -> P x (refl A x).

Arguments J {_ _ _}.

Arguments J_r {_ _ _}.

Register Has_J as rocq.core.Has_J.

Register Has_J_r as rocq.core.Has_J_r.

Register Has_J_forward as rocq.core.Has_J_forward.

Register Has_J_r_forward as rocq.core.Has_J_r_forward.

Class Has_Leibniz@{sa se sp;la le lp} (eq : forall A : Type@{sa ; la}, A -> A -> Type@{se;le}) :=
  leibniz : forall (A : Type@{sa ; la}) (x : A) (P : A -> Type@{sp ; lp}), P x -> forall y, eq A x y -> P y.

Class Has_Leibniz_r@{sa se sp;la le lp} (eq : forall A : Type@{sa ; la}, A -> A -> Type@{se;le}) :=
  leibniz_r : forall (A : Type@{sa ; la}) (x : A) (P : A -> Type@{sp ; lp}), P x -> forall y, eq A y x -> P y.

Arguments leibniz _ {_}.

Register Has_Leibniz as rocq.core.Has_Leibniz.
Register Has_Leibniz_r as rocq.core.Has_Leibniz_r.

Definition J_no_dep@{s s' sp;l l' lp} {eq} {refl} (eqr : Has_J@{s s' sp;l l' lp} eq refl) :
  forall (A : Type@{s ; l}) (x : A) (P : A -> Type@{sp ; lp}), P x -> forall y (e : eq A x y), P y :=
  fun A x P px y e => J _ x (fun y _ => P y) px y e.

Instance Has_J_Has_Leibniz@{s s' sp;l l' lp} {eq} {refl} (eqr : Has_J@{s s' sp;l l' lp} eq refl) : Has_Leibniz@{s s' sp;l l' lp} eq :=
  fun A x P px y e => J_no_dep eqr A x P px y e.

Instance Has_J_r_Has_Leibniz_r@{s s' sp;l l' lp} {eq} {refl} (eqr : Has_J_r@{s s' sp;l l' lp} eq refl) : Has_Leibniz_r@{s s' sp;l l' lp} eq :=
  fun A x P px y e => J_no_dep eqr A x P px y e.

#[projections(primitive=no)]
Class Has_JRefl@{sa se se' se'';la le le' le''}
  (eq : forall A : Type@{sa ; la}, A -> A -> Type@{se;le})
  (Has_refl : Has_refl@{sa se;la le} eq)
  (Has_J : Has_J@{sa se se';la le le'} eq Has_refl)
  (eqe : forall A : Type@{se' ; le'}, A -> A -> Type@{se'';le''}) : Type
  :=
  {
    J_refl : forall (A : Type@{sa ; la}) (x : A) (P : forall y : A, eq A x y -> Type@{se' ; le'}) (f : P x (refl A x)), eqe _ (J A x P f x (refl A x)) f ;
    leibniz_refl : forall (A : Type@{sa ; la}) (x : A) (P : A -> Type@{se' ; le'}) (f : P x), eqe _ (leibniz eq A x P f x (refl A x)) f
  }.

Register Has_JRefl as rocq.core.Has_JRefl.

End J_as_a_class.


Section ap.
  Sort sa se sb se'.
  Universe la le lb le'.
  Context {eq : forall A : Type@{sa;la}, A -> A -> Type@{se;le}}
          {A : Type@{sa;la}}
          {eq' : forall A : Type@{sb; lb}, A -> A -> Type@{se';le'}}
          {_refl: Has_refl@{sb se';lb le'} eq'}
          {_leibniz: Has_Leibniz@{sa se se';la le le'} eq}.

  Definition ap {B} (f : A -> B) {x y : A} (e : eq _ x y) : eq' _ (f x) (f y) :=
    leibniz _ _ (fun y => eq' B (f x) (f y)) (refl _ _) _ e.

End ap.

Register ap as core.eq.congr.

Section sym.
  Sort sa se.
  Universe la le.
  Context {eq : forall A : Type@{sa;la}, A -> A -> Type@{se;le}}
          {A : Type@{sa;la}}
          {_refl: Has_refl@{sa se;la le} eq}
          {_leibniz: Has_Leibniz@{sa se se;la le le} eq}.

  Definition sym {x y : A} (e : eq _ x y) : eq _ y x :=
    leibniz _ _ (fun y => eq A y _) (refl _ _) _ e.

End sym.

Instance Has_J_Has_J_forward@{sa se sp;la le lp} eq Has_refl
  {has_J : Has_J@{sa se sp;la le lp} eq Has_refl} : Has_J_forward@{sa se sp;la le lp} eq Has_refl :=
  fun A x P y e => J _ _ (fun y e => P y e -> P _ _) (fun x => x) _ _.

Instance Has_J_r_Has_J_r_forward@{sa se sp;la le lp} eq Has_refl
  {has_J : Has_J_r@{sa se sp;la le lp} eq Has_refl} : Has_J_r_forward@{sa se sp;la le lp} eq Has_refl :=
  fun A x P y e => J_r _ _ (fun y e => P y e -> P _ _) (fun x => x) _ _.

Unset Universe Polymorphism.
