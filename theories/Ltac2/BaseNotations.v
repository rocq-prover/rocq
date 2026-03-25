(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ltac2.Init.

(** This file is meant to contain only notations that do not make any valid
Ltac2 identifiers difficult or impossible to use. *)

(* [f @@ g @@ h @@ x] is equivalent to [f (g (h x))] up to evaluation order of subterms. *)
Ltac2 Notation f(self) "@@" x(self) : 2 := f x. (* right associative *)

(* [x |> h |> g |> f] is equivalent to [f (g (h x))] up to evaluation order of subterms. *)
Ltac2 Notation x(self) "|>" f(self) : 3 := f x. (* left associative *)
