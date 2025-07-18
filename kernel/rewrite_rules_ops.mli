(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Sorts
open Declarations
open Constr

module QState : sig
  type t
  val to_pair : t -> Quality.t QVar.Map.t * QVar.Set.t
  val of_pair : 'a QVar.Map.t -> Quality.t QVar.Map.t * QVar.Set.t -> t
end

type extra_env

module ExtraEnv : sig
  val sigma_of : extra_env -> Typeops.evar_handler
end


val typecheck_pattern : Environ.env -> pattern -> extra_env * Environ.unsafe_judgment


val evar_handler : CClosure.evar_handler

val check_inferred_constraints: Environ.env -> extra_env -> rewrite_rule_info -> unit

val check_pattern_relevances : extra_env -> relevance -> unit

val check_pattern_redex : Environ.env -> Declarations.pattern -> unit

val nf_evar : rewrite_rule_info -> constr -> constr


type pattern_translation_error =
  | UnknownEvar
  | UnknownQVar of Sorts.QVar.t
  | UnknownLevel of Univ.Level.t
  | DuplicatePatVar of Evar.t * Names.Id.t * int * int
  | DuplicateQVar of Sorts.QVar.t * int * int
  | DuplicateUVar of Univ.Level.t * int * int
  | NoHeadSymbol

exception PatternTranslationError of pattern_translation_error

val translate_rewrite_rule : Environ.env -> rewrite_rule -> Names.Constant.t * machine_rewrite_rule

val head_symbol : pattern -> Names.Constant.t
