(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Corelib Require Import PosDef IntDef.

(** * Rational numbers to serve as interface for the micromega plugin

Beware: this type is useful for effective computations but it is
known that attempting any proof on rational numbers using it
is a very bad idea, due to its lack of canonicity
(for instance 2/3 and 4/6 are not definitionally equal). *)

(** Rationals are pairs of [Z] and [positive] numbers. *)

Record Q : Set := Qmake {Qnum : Z; Qden : positive}.

Register Q as rat.Q.type.
Register Qmake as rat.Q.Qmake.

Definition Qeq_bool x y :=
  Z.eqb (Z.mul (Qnum x) (Zpos (Qden y))) (Z.mul (Qnum y) (Zpos (Qden x))).

Definition Qle_bool x y :=
  Z.leb (Z.mul (Qnum x) (Zpos (Qden y))) (Z.mul (Qnum y) (Zpos (Qden x))).

(** * Addition, multiplication and opposite *)

(** The addition, multiplication and opposite are defined
   in the straightforward way: *)

Definition Qplus (x y : Q) :=
  Qmake (Z.add (Z.mul (Qnum x) (Zpos (Qden y))) (Z.mul (Qnum y) (Zpos (Qden x))))
    (Pos.mul (Qden x) (Qden y)).

Definition Qmult (x y : Q) :=
  Qmake (Z.mul (Qnum x) (Qnum y)) (Pos.mul (Qden x) (Qden y)).

Definition Qopp (x : Q) := Qmake (Z.opp (Qnum x)) (Qden x).

Definition Qminus (x y : Q) := Qplus x (Qopp y).

Definition Qinv (x : Q) :=
  match Qnum x with
  | Z0 => Qmake Z0 1
  | Zpos p => Qmake (Zpos (Qden x)) p
  | Zneg p => Qmake (Zneg (Qden x)) p
  end.

Definition Q0 := Qmake Z0 xH.
Definition Q1 := Qmake (Zpos xH) xH.
