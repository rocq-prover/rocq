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
open EConstr
open Environ
open Evd

(** Eliminations *)

type dep_flag = bool

(** Build a case analysis elimination scheme in some sort *)

type case_analysis = private {
  case_params : EConstr.rel_context;
  case_pred : Name.t EConstr.binder_annot * EConstr.types;
  case_branches : EConstr.rel_context;
  case_arity : EConstr.rel_context;
  case_body : EConstr.t;
  case_type : EConstr.t;
}

val eval_case_analysis : case_analysis -> EConstr.t * EConstr.types

val default_case_analysis_dependence : env -> inductive -> bool

val build_case_analysis_scheme : env -> Evd.evar_map -> inductive puniverses ->
  dep_flag -> ESorts.t -> evar_map * case_analysis

(** Build a dependent case elimination predicate unless type is in Prop
   or is a recursive record with primitive projections. *)

val build_case_analysis_scheme_default : env -> evar_map -> inductive puniverses ->
  ESorts.t -> evar_map * case_analysis

(** Builds a recursive induction scheme (Peano-induction style) in the given sort.  *)

val build_induction_scheme : env -> evar_map -> inductive puniverses ->
  dep_flag -> ESorts.t -> evar_map * constr

(** Builds mutual (recursive) induction schemes *)

val build_mutual_induction_scheme :
  env -> evar_map -> ?force_mutual:bool ->
  (inductive * dep_flag * EConstr.ESorts.t) list -> einstance -> evar_map * constr list

(** Default dependence of eliminations for Prop inductives *)

val declare_prop_but_default_dependent_elim : inductive -> unit

val is_prop_but_default_dependent_elim : inductive -> bool

val pseudo_sort_quality_for_elim : inductive -> Declarations.one_inductive_body -> Sorts.Quality.t
