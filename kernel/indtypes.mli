(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Declarations
open Environ
open Entries
open Constr

(** Computes which uniform parameters are strictly positive in a mutual inductive block.
    [inds : (rel_context * (rel_declaration list * types) array) array] contains
    the context of indices, then for each constructor the telescope of arguments, and the head.
    This function can be used whether the inductive is refered using [Rel] or [Ind]. *)
val compute_params_rec_strpos : env -> MutInd.t -> rel_context -> rel_context -> int -> int ->
    (rel_context * (rel_declaration list * types) array) array -> bool list

(** Check if an inductive definition is well-typed and positive, and
    computes the associated mutual inductive body. *)
val check_inductive : env -> sec_univs:UVars.Instance.t option
  -> MutInd.t -> mutual_inductive_entry
  -> mutual_inductive_body * IndTyping.NotPrimRecordReason.t option
