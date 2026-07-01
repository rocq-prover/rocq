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

Create HintDb typeclass_instances discriminated.
Create HintDb rewrite_instances discriminated.

Hint Constants Opaque : rewrite_instances.
Hint Projections Opaque : rewrite_instances.
Hint Variables Opaque : rewrite_instances.

Local Set Universe Polymorphism.

Class Has_refl@{sa se;la le} (eq : forall A : Univ@{sa;la}, A -> A -> Univ@{se;le})
:= refl : forall A x, eq A x x.

(* This class register a Martin-Löf like elimination principle *)

Class Has_J@{sa se sp;la le lp} (eq : forall A : Univ@{sa ; la}, A -> A -> Univ@{se;le})
  (Has_refl : Has_refl eq) :=
  J_eliminator : forall (A : Univ@{sa ; la}) (x : A) (P : forall y : A, eq A x y -> Univ@{sp ; lp}),
    P x (refl A x) -> forall y e, P y e.

(* This class is for forward dependent rewriting *)

Class Has_J_r@{sa se sp;la le lp} (eq : forall A : Univ@{sa ; la}, A -> A -> Univ@{se;le})
  (Has_refl : Has_refl eq) :=
  J_r_eliminator: forall (A : Univ@{sa ; la}) (x : A) (P : forall y : A, eq A y x -> Univ@{sp ; lp}),
    P x (refl A x) -> forall y e, P y e.

(* Those two classes are for dependent rewriting in an hypotesis *)

Class Has_J_forward@{sa se sp;la le lp} (eq : forall A : Univ@{sa ; la}, A -> A -> Univ@{se;le})
  (Has_refl : Has_refl eq) :=
  J_forward : forall (A : Univ@{sa ; la}) (x : A) (P : forall y : A, eq A x y -> Univ@{sp ; lp}) y e,
    P y e -> P x (refl A x).

Class Has_J_r_forward@{sa se sp;la le lp} (eq : forall A : Univ@{sa ; la}, A -> A -> Univ@{se;le})
  (Has_refl : Has_refl eq) :=
  J_r_forward : forall (A : Univ@{sa ; la}) (x : A) (P : forall y : A, eq A y x -> Univ@{sp ; lp}) y e,
    P y e -> P x (refl A x).

(* Those two classes are for non-dependent rewriting *)

Class Has_Leibniz@{sa se sp;la le lp} (eq : forall A : Univ@{sa ; la}, A -> A -> Univ@{se;le}) :=
  leibniz : forall (A : Univ@{sa ; la}) (x : A) (P : A -> Univ@{sp ; lp}), P x -> forall y, eq A x y -> P y.

Class Has_Leibniz_r@{sa se sp;la le lp} (eq : forall A : Univ@{sa ; la}, A -> A -> Univ@{se;le}) :=
  leibniz_r : forall (A : Univ@{sa ; la}) (x : A) (P : A -> Univ@{sp ; lp}), P x -> forall y, eq A y x -> P y.

Register Has_refl as core.Has_refl.
Typeclasses Opaque Has_refl.

Register Has_J as core.Has_J.
Typeclasses Opaque Has_J.

Register Has_J_r as core.Has_J_r.
Typeclasses Opaque Has_J_r.

Register Has_J_forward as core.Has_J_forward.
Typeclasses Opaque Has_J_forward.

Register Has_J_r_forward as core.Has_J_r_forward.
Typeclasses Opaque Has_J_r_forward.

Register Has_Leibniz as core.Has_Leibniz.
Typeclasses Opaque Has_Leibniz.

Register Has_Leibniz_r as core.Has_Leibniz_r.
Typeclasses Opaque Has_Leibniz_r.

Definition J_no_dep@{s s' sp;l l' lp} {eq} {refl} (eqr : Has_J@{s s' sp;l l' lp} eq refl) :
  forall (A : Univ@{s ; l}) (x : A) (P : A -> Univ@{sp ; lp}), P x -> forall y (e : eq A x y), P y :=
  fun A x P px y e => J_eliminator _ x (fun y _ => P y) px y e.

Definition Has_J_Has_Leibniz@{s s' sp;l l' lp} {eq} {refl} (eqr : Has_J@{s s' sp;l l' lp} eq refl) : Has_Leibniz@{s s' sp;l l' lp} eq :=
 fun A x P px y e => J_no_dep eqr A x P px y e.

Section ap.
  Sort sa se sb se'.
  Universe la le lb le'.
  Context {eq : forall A : Univ@{sa;la}, A -> A -> Univ@{se;le} }
          {eq' : forall A : Univ@{sb; lb}, A -> A -> Univ@{se';le'} }
          {_refl: Has_refl@{sb se';lb le'} eq'}
          {_leibniz: Has_Leibniz@{sa se se';la le le'} eq}.

  Definition ap [A : Univ@{sa;la}] [B:Univ@{sb;lb}] (f : A -> B) [x y : A] (e : eq _ x y) : eq' _ (f x) (f y) :=
    leibniz A x (fun y => eq' B (f x) (f y)) (refl _ _) y e.

End ap.

Register ap as core.ap.

Section sym.
  Sort sa se.
  Universe la le.
  Context {eq : forall A : Univ@{sa;la}, A -> A -> Univ@{se;le} }
          {A : Univ@{sa;la} }
          {_refl: Has_refl@{sa se;la le} eq}
          {_leibniz: Has_Leibniz@{sa se se;la le le} eq}.

  Definition sym {x y : A} (e : eq _ x y) : eq _ y x :=
    leibniz _ _ (fun y => eq A y _) (refl _ _) _ e.

End sym.

Definition Has_J_Has_J_forward@{sa se sp;la le lp} eq Has_refl
  {has_J : Has_J@{sa se sp;la le lp} eq Has_refl} :
  forall (A : Univ@{sa ; la}) (x : A) (P : forall y : A, eq A x y -> Univ@{sp ; lp}) y e,
      P y e -> P x (refl A x) :=
  fun A x P y e => J_eliminator _ _ (fun y e => P y e -> P _ _) (fun x => x) _ _.

Definition _Has_J_Has_J_forward@{sa se sp;la le lp} eq Has_refl
  {has_J : Has_J@{sa se sp;la le lp} eq Has_refl} : Has_J_forward@{sa se sp;la le lp} eq Has_refl
  := Has_J_Has_J_forward _ _.

Hint Resolve _Has_J_Has_J_forward : rewrite_instances.

Definition Has_J_r_Has_J_r_forward@{sa se sp;la le lp} eq Has_refl
  {has_J : Has_J_r@{sa se sp;la le lp} eq Has_refl} :
  forall (A : Univ@{sa ; la}) (x : A) (P : forall y : A, eq A y x -> Univ@{sp ; lp}) y e,
      P y e -> P x (refl A x) :=
  fun A x P y e => J_r_eliminator _ _ (fun y e => P y e -> P _ _) (fun x => x) _ _.

Definition _Has_J_r_Has_J_r_forward@{sa se sp;la le lp} eq Has_refl
  {has_J : Has_J_r@{sa se sp;la le lp} eq Has_refl} : Has_J_r_forward@{sa se sp;la le lp} eq Has_refl
  := Has_J_r_Has_J_r_forward _ _.

Hint Resolve _Has_J_r_Has_J_r_forward : rewrite_instances.
