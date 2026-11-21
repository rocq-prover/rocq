(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Rust implementation of the kernel conversion. *)

val conv : typed:bool -> RedFlags.reds -> int -> bool -> CClosure.evar_handler ->
  Environ.env -> UGraph.t -> 'a -> 'check -> Constr.t -> Constr.t ->
  ('a, 'err option) result
(** [conv ~typed reds cv_pb l2r evars env graph state check t1 t2] where
    [check] is a [('a, 'err) Conversion.universe_compare] and [cv_pb] is 0
    for [CONV] and 1 for [CUMUL]. *)
