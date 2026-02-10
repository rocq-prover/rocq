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
open Tactypes
open EConstr

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

val strategy_of_ast :
  (Glob_term.glob_constr * constr delayed_open, Pattern.constr_pattern, Redexpr.red_expr delayed_open, Id.t, unit Proofview.tactic) strategy_ast ->
  Rewrite.strategy

val map_strategy : ('a -> 'b) -> ('c -> 'd) -> ('e -> 'f) -> ('g -> 'h) -> ('i -> 'j) ->
  ('a, 'c, 'e, 'g, 'i) strategy_ast -> ('b, 'd, 'f, 'h, 'j) strategy_ast

val pr_strategy : ('a -> Pp.t) -> ('b -> Pp.t) -> ('c -> Pp.t) -> ('d -> Pp.t) -> ('e -> Pp.t) ->
  ('a, 'b, 'c, 'd, 'e) strategy_ast -> Pp.t
