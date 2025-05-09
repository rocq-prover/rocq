(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*s Extraction from Rocq terms to Miniml. *)

open Names
open Declarations
open Environ
open Evd
open Miniml

val extract_constant : Common.State.t -> Global.indirect_accessor -> env -> Constant.t -> constant_body -> ml_decl

val extract_constant_spec : Common.State.t -> env -> Constant.t -> ('a, 'b) pconstant_body -> ml_spec

(** For extracting "module ... with ..." declaration *)

val extract_with_type :
  Common.State.t -> env -> evar_map -> EConstr.t -> ( Id.t list * ml_type ) option

val extract_fixpoint :
  Common.State.t -> env -> evar_map -> Constant.t array -> EConstr.rec_declaration -> ml_decl

val extract_inductive : Common.State.t -> env -> MutInd.t -> ml_ind

(** For Extraction Compute and Show Extraction *)

val extract_constr : Common.State.t -> env -> evar_map -> EConstr.t -> ml_ast * ml_type

(*s Is a [ml_decl] or a [ml_spec] logical ? *)

val logical_decl : ml_decl -> bool
val logical_spec : ml_spec -> bool
