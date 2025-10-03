(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Notations.
Require Import Ltac.

Notation "A -> B" := (forall (_ : A), B) : type_scope.

Create HintDb typeclass_instances discriminated.
Create HintDb rewrite_instances discriminated.

Hint Constants Opaque : rewrite_instances.
Hint Projections Opaque : rewrite_instances.
Hint Variables Opaque : rewrite_instances.

Local Set Universe Polymorphism.

Class Has_refl@{sa se;la le} (eq : forall A : Type@{sa;la}, A -> A -> Type@{se;le})
:= refl : forall A x, eq A x x.

(* This class register a Martin-Löf like elimination principle *)

Class Has_J@{sa se sp;la le lp} (eq : forall A : Type@{sa ; la}, A -> A -> Type@{se;le})
  (Has_refl : Has_refl eq) :=
  J_eliminator : forall (A : Type@{sa ; la}) (x : A) (P : forall y : A, eq A x y -> Type@{sp ; lp}),
    P x (refl A x) -> forall y e, P y e.

(* This class is for forward dependent rewriting *)

Class Has_J_r@{sa se sp;la le lp} (eq : forall A : Type@{sa ; la}, A -> A -> Type@{se;le})
  (Has_refl : Has_refl eq) :=
  J_r_eliminator: forall (A : Type@{sa ; la}) (x : A) (P : forall y : A, eq A y x -> Type@{sp ; lp}),
    P x (refl A x) -> forall y e, P y e.

(* Those two classes are for dependent rewriting in an hypotesis *)

Class Has_J_forward@{sa se sp;la le lp} (eq : forall A : Type@{sa ; la}, A -> A -> Type@{se;le})
  (Has_refl : Has_refl eq) :=
  J_forward : forall (A : Type@{sa ; la}) (x : A) (P : forall y : A, eq A x y -> Type@{sp ; lp}) y e,
    P y e -> P x (refl A x).

Class Has_J_r_forward@{sa se sp;la le lp} (eq : forall A : Type@{sa ; la}, A -> A -> Type@{se;le})
  (Has_refl : Has_refl eq) :=
  J_r_forward : forall (A : Type@{sa ; la}) (x : A) (P : forall y : A, eq A y x -> Type@{sp ; lp}) y e,
    P y e -> P x (refl A x).

(* Those two classes are for non-dependent rewriting *)

Class Has_Leibniz@{sa se sp;la le lp} (eq : forall A : Type@{sa ; la}, A -> A -> Type@{se;le}) :=
  leibniz : forall (A : Type@{sa ; la}) (x : A) (P : A -> Type@{sp ; lp}), P x -> forall y, eq A x y -> P y.

Class Has_Leibniz_r@{sa se sp;la le lp} (eq : forall A : Type@{sa ; la}, A -> A -> Type@{se;le}) :=
  leibniz_r : forall (A : Type@{sa ; la}) (x : A) (P : A -> Type@{sp ; lp}), P x -> forall y, eq A y x -> P y.

Register Has_refl as rocq.core.Has_refl.
Typeclasses Opaque Has_refl.

Register Has_J as rocq.core.Has_J.
Typeclasses Opaque Has_J.

Register Has_J_r as rocq.core.Has_J_r.
Typeclasses Opaque Has_J_r.

Register Has_J_forward as rocq.core.Has_J_forward.
Typeclasses Opaque Has_J_forward.

Register Has_J_r_forward as rocq.core.Has_J_r_forward.
Typeclasses Opaque Has_J_r_forward.

Register Has_Leibniz as rocq.core.Has_Leibniz.
Typeclasses Opaque Has_Leibniz.

Register Has_Leibniz_r as rocq.core.Has_Leibniz_r.
Typeclasses Opaque Has_Leibniz_r.

Definition J_no_dep@{s s' sp;l l' lp} {eq} {refl} (eqr : Has_J@{s s' sp;l l' lp} eq refl) :
  forall (A : Type@{s ; l}) (x : A) (P : A -> Type@{sp ; lp}), P x -> forall y (e : eq A x y), P y :=
  fun A x P px y e => J_eliminator _ x (fun y _ => P y) px y e.

Definition Has_J_Has_Leibniz@{s s' sp;l l' lp} {eq} {refl} (eqr : Has_J@{s s' sp;l l' lp} eq refl) : Has_Leibniz@{s s' sp;l l' lp} eq :=
 fun A x P px y e => J_no_dep eqr A x P px y e.

Section ap.
  Sort sa se sb se'.
  Universe la le lb le'.
  Context {eq : forall A : Type@{sa;la}, A -> A -> Type@{se;le} }
          {eq' : forall A : Type@{sb; lb}, A -> A -> Type@{se';le'} }
          {_refl: Has_refl@{sb se';lb le'} eq'}
          {_leibniz: Has_Leibniz@{sa se se';la le le'} eq}.

  Definition ap [A : Type@{sa;la}] [B:Type@{sb;lb}] (f : A -> B) [x y : A] (e : eq _ x y) : eq' _ (f x) (f y) :=
    leibniz A x (fun y => eq' B (f x) (f y)) (refl _ _) y e.

End ap.

Register ap as rocq.core.ap.

Section sym.
  Sort sa se.
  Universe la le.
  Context {eq : forall A : Type@{sa;la}, A -> A -> Type@{se;le} }
          {A : Type@{sa;la} }
          {_refl: Has_refl@{sa se;la le} eq}
          {_leibniz: Has_Leibniz@{sa se se;la le le} eq}.

  Definition sym {x y : A} (e : eq _ x y) : eq _ y x :=
    leibniz _ _ (fun y => eq A y _) (refl _ _) _ e.

End sym.

Definition Has_J_Has_J_forward@{sa se sp;la le lp} eq Has_refl
  {has_J : Has_J@{sa se sp;la le lp} eq Has_refl} :
  forall (A : Type@{sa ; la}) (x : A) (P : forall y : A, eq A x y -> Type@{sp ; lp}) y e,
      P y e -> P x (refl A x) :=
  fun A x P y e => J_eliminator _ _ (fun y e => P y e -> P _ _) (fun x => x) _ _.

Definition _Has_J_Has_J_forward@{sa se sp;la le lp} eq Has_refl
  {has_J : Has_J@{sa se sp;la le lp} eq Has_refl} : Has_J_forward@{sa se sp;la le lp} eq Has_refl
  := Has_J_Has_J_forward _ _.

Hint Resolve _Has_J_Has_J_forward : rewrite_instances.

Definition Has_J_r_Has_J_r_forward@{sa se sp;la le lp} eq Has_refl
  {has_J : Has_J_r@{sa se sp;la le lp} eq Has_refl} :
  forall (A : Type@{sa ; la}) (x : A) (P : forall y : A, eq A y x -> Type@{sp ; lp}) y e,
      P y e -> P x (refl A x) :=
  fun A x P y e => J_r_eliminator _ _ (fun y e => P y e -> P _ _) (fun x => x) _ _.

Definition _Has_J_r_Has_J_r_forward@{sa se sp;la le lp} eq Has_refl
  {has_J : Has_J_r@{sa se sp;la le lp} eq Has_refl} : Has_J_r_forward@{sa se sp;la le lp} eq Has_refl
  := Has_J_r_Has_J_r_forward _ _.

Hint Resolve _Has_J_r_Has_J_r_forward : rewrite_instances.
