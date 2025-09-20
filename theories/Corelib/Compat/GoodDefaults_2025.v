(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Good defaults 2025

  File exporting recommended option settings at the time of releasing Rocq v9.1

*)

#[ export ] Set Default Goal Selector "!".

#[ export ] Set Asymmetric Patterns.

#[ export ] Set Keyed Unification.

(** The following affect people using [Universe Polymorphism]. *)

#[ export ] Set Polymorphic Inductive Cumulativity.

#[ export ] Set Typeclasses Default Mode "!".
Hint Constants Opaque : typeclass_instances.

Ltac Tauto.intuition_solver ::= auto with core.

(** Makes the behavior of [injection] consistent with the rest of standard
  tactics.
*)

#[ export ] Set Structural Injection.

(** These three affect pepole that set [Implicit Arguments]. *)

#[ export ] Set Strongly Strict Implicit.
#[ export ] Set Maximal Implicit Insertion.
#[ export ] Set Contextual Implicit.
