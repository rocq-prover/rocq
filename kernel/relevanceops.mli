(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Compute relevance from the term's checked type. Unsafe casts can affect
    relevance indirectly through types, so following only the operand or head
    is insufficient. Callers already holding a checked type judgment should
    obtain relevance directly from its sort instead of rechecking the term. *)

val relevance_of_term : Environ.env -> Constr.constr -> Sorts.relevance

(** Helpers *)
open Names
val relevance_of_rel : Environ.env -> int -> Sorts.relevance
val relevance_of_var : Environ.env -> Id.t -> Sorts.relevance
val relevance_of_constant : Environ.env -> Constr.pconstant -> Sorts.relevance
val relevance_of_constructor : Environ.env -> Constr.pconstructor -> Sorts.relevance
val relevance_of_projection_repr : Environ.env -> Projection.Repr.t UVars.puniverses -> Sorts.relevance
val relevance_of_projection : Environ.env -> Projection.t UVars.puniverses -> Sorts.relevance
