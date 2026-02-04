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
open Environ
open EConstr
open Evd
open Tactypes

(** TODO: document and clean me! *)

exception RewriteFailure of Environ.env * Evd.evar_map * Pretype_errors.pretype_error

type unary_strategy =
    Subterms | Subterm | Innermost | Outermost
  | Bottomup | Topdown | Progress | Try | Any | Repeat

type binary_strategy =
  | Compose

type nary_strategy = Choice

type ('constr,'constr_pattern,'redexpr,'id,'tactic) strategy_ast =
  | StratId | StratFail | StratRefl
  | StratUnary of unary_strategy * ('constr,'constr_pattern,'redexpr,'id,'tactic) strategy_ast
  | StratBinary of
      binary_strategy * ('constr,'constr_pattern,'redexpr,'id,'tactic) strategy_ast * ('constr,'constr_pattern,'redexpr,'id,'tactic) strategy_ast
  | StratNAry of nary_strategy * ('constr,'constr_pattern,'redexpr,'id,'tactic) strategy_ast list
  | StratConstr of 'constr * bool
  | StratTerms of 'constr list
  | StratHints of bool * string
  | StratEval of 'redexpr
  | StratFold of 'constr
  | StratVar of 'id
  | StratFix of 'id * ('constr,'constr_pattern,'redexpr,'id,'tactic) strategy_ast
  | StratMatches of 'constr_pattern
  | StratTactic of 'tactic
type rewrite_proof =
  | RewPrf of constr * constr
  | RewCast of Constr.cast_kind

type evars = evar_map * Evar.Set.t (* goal evars, constraint evars *)

type rewrite_result_info =
  { rew_rel: constr; rew_to : constr; rew_prf : constr }

type rewrite_result =
| Fail
| Identity
| Success of rewrite_result_info

val subst_rewrite_result : Evd.evar_map -> (Id.t -> constr) -> rewrite_result -> rewrite_result

type strategy

val strategy_of_ast : (Glob_term.glob_constr * constr delayed_open, Pattern.constr_pattern, Redexpr.red_expr delayed_open, Id.t, unit Proofview.tactic) strategy_ast -> strategy

val map_strategy : ('a -> 'b) -> ('c -> 'd) -> ('e -> 'f) -> ('g -> 'h) -> ('i -> 'j) ->
  ('a, 'c, 'e, 'g, 'i) strategy_ast -> ('b, 'd, 'f, 'h, 'j) strategy_ast

val pr_strategy : ('a -> Pp.t) -> ('b -> Pp.t) -> ('c -> Pp.t) -> ('d -> Pp.t) -> ('e -> Pp.t) ->
  ('a, 'b, 'c, 'd, 'e) strategy_ast -> Pp.t

(** Entry point for user-level "rewrite_strat" *)
val cl_rewrite_clause_strat : strategy -> Id.t option -> unit Proofview.tactic

(** Entry point for user-level "setoid_rewrite" *)
val cl_rewrite_clause :
  EConstr.t with_bindings delayed_open ->
  bool -> Locus.occurrences -> Id.t option -> unit Proofview.tactic

val is_applied_rewrite_relation :
  env -> evar_map -> rel_context -> constr -> types option

val get_reflexive_proof : env -> evar_map -> constr -> constr -> evar_map * constr

val get_symmetric_proof : env -> evar_map -> constr -> constr -> evar_map * constr

val get_transitive_proof : env -> evar_map -> constr -> constr -> evar_map * constr

val setoid_symmetry : unit Proofview.tactic

val setoid_symmetry_in : Id.t -> unit Proofview.tactic

val setoid_reflexivity : unit Proofview.tactic

val setoid_transitivity : constr option -> unit Proofview.tactic

module Strategies :
sig
  val fail : strategy
  val id : strategy
  val refl : strategy
  val progress : strategy -> strategy
  val seq : strategy -> strategy -> strategy
  val seqs : strategy list -> strategy
  val choice : strategy -> strategy -> strategy
  val choices : strategy list -> strategy
  val try_ : strategy -> strategy

  val fix_tac : (strategy -> strategy Proofview.tactic) -> strategy Proofview.tactic
  val fix : (strategy -> strategy) -> strategy

  val any : strategy -> strategy
  val repeat : strategy -> strategy
  val all_subterms : strategy -> strategy
  val one_subterm : strategy -> strategy
  val bottomup : strategy -> strategy
  val topdown : strategy -> strategy
  val innermost : strategy -> strategy
  val outermost : strategy -> strategy

  val one_lemma : delayed_open_constr -> bool -> Gentactic.glob_generic_tactic option -> Locus.occurrences -> strategy
  val lemmas : (delayed_open_constr * bool * Gentactic.glob_generic_tactic option) list -> strategy

  val old_hints : string -> strategy
  val hints : string -> strategy
  val reduce : Redexpr.red_expr -> strategy

  val fold : Evd.econstr -> strategy
  val fold_glob : Glob_term.glob_constr -> strategy

  val matches : Pattern.constr_pattern -> strategy

  val tactic_call : (env:Environ.env -> carrier:constr -> lhs:constr -> rel:constr option -> rewrite_result Proofview.tactic) -> strategy
end

module Internal :
sig
val build_signature :
  Environ.env -> Evd.evar_map -> constr ->
  (types * types option) option list ->
  (types * types option) option ->
  Evd.evar_map * constr * (constr * t option) list
val build_morphism_signature : Environ.env -> Evd.evar_map -> Constrexpr.constr_expr -> Evd.evar_map * t
val default_morphism : Environ.env -> Evd.evar_map ->
  (types * types option) option list *
  (types * types option) option ->
  constr -> Evd.evar_map * constr * t
end
