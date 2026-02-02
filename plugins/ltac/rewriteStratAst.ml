(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Names
open Rewrite

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

let rec map_strategy f g h i j = function
  | StratId | StratFail | StratRefl as s -> s
  | StratUnary (s, str) -> StratUnary (s, map_strategy f g h i j str)
  | StratBinary (s, str, str') -> StratBinary (s, map_strategy f g h i j str, map_strategy f g h i j str')
  | StratNAry (s, strs) -> StratNAry (s, List.map (map_strategy f g h i j) strs)
  | StratConstr (c, b) -> StratConstr (f c, b)
  | StratTerms l -> StratTerms (List.map f l)
  | StratHints (b, id) -> StratHints (b, id)
  | StratEval r -> StratEval (h r)
  | StratFold c -> StratFold (f c)
  | StratVar id -> StratVar (i id)
  | StratFix (id, s) -> StratFix (i id, map_strategy f g h i j s)
  | StratMatches c -> StratMatches (g c)
  | StratTactic t -> StratTactic (j t)

let pr_ustrategy = function
| Subterms -> str "subterms"
| Subterm -> str "subterm"
| Innermost -> str "innermost"
| Outermost -> str "outermost"
| Bottomup -> str "bottomup"
| Topdown -> str "topdown"
| Progress -> str "progress"
| Try -> str "try"
| Any -> str "any"
| Repeat -> str "repeat"

let paren p = str "(" ++ p ++ str ")"

let rec pr_strategy0 prc prcp prr prid prtac = function
| StratId -> str "id"
| StratFail -> str "fail"
| StratRefl -> str "refl"
| str -> paren (pr_strategy prc prcp prr prid prtac str)

and pr_strategy1 prc prcp prr prid prtac = function
| StratUnary (s, str) ->
  pr_ustrategy s ++ spc () ++ pr_strategy1 prc prcp prr prid prtac str
| StratNAry (Choice, strs) ->
  str "choice" ++ brk (1,2) ++ prlist_with_sep spc (fun str -> hov 0 (pr_strategy0 prc prcp prr prid prtac str)) strs
| StratConstr (c, true) -> prc c
| StratConstr (c, false) -> str "<-" ++ spc () ++ prc c
| StratVar id -> prid id
| StratTerms cl -> str "terms" ++ spc () ++ pr_sequence prc cl
| StratHints (old, id) ->
  let cmd = if old then "old_hints" else "hints" in
  str cmd ++ spc () ++ str id
| StratEval r -> str "eval" ++ spc () ++ prr r
| StratFold c -> str "fold" ++ spc () ++ prc c
| StratMatches p -> str "pattern" ++ spc () ++ prcp p
| StratTactic t -> str"tactic" ++ spc () ++ prtac t
| str -> pr_strategy0 prc prcp prr prid prtac str

and pr_strategy2 prc prcp prr prid prtac = function
| StratBinary (Compose, str1, str2) ->
  pr_strategy2 prc prcp prr prid prtac str1 ++ str ";" ++ spc () ++ hov 0 (pr_strategy1 prc prcp prr prid prtac str2)
| str -> hov 0 (pr_strategy1 prc prcp prr prid prtac str)

and pr_strategy prc prcp prr prid prtac = function
| StratFix (id,s) -> str "fix" ++ spc() ++ prid id ++ spc() ++ str ":=" ++ spc() ++ hov 0 (pr_strategy1 prc prcp prr prid prtac s)
| str -> pr_strategy2 prc prcp prr prid prtac str

let strategy_of_ast bindings strat =
  let rec aux bindings = function
  | StratId -> Strategies.id
  | StratFail -> Strategies.fail
  | StratRefl -> Strategies.refl
  | StratUnary (f, s) ->
    let s' = aux bindings s in
    let f' = match f with
      | Subterms -> Strategies.all_subterms
      | Subterm -> Strategies.one_subterm
      | Innermost -> Strategies.innermost
      | Outermost -> Strategies.outermost
      | Bottomup -> Strategies.bottomup
      | Topdown -> Strategies.topdown
      | Progress -> Strategies.progress
      | Try -> Strategies.try_
      | Any -> Strategies.any
      | Repeat -> Strategies.repeat
    in f' s'
  | StratBinary (f, s, t) ->
    let s' = aux bindings s in
    let t' = aux bindings t in
    let f' = match f with
      | Compose -> Strategies.seq
    in f' s' t'
  | StratNAry (Choice, strs) ->
    let strs = List.map (aux bindings) strs in
    begin match strs with
      | [] -> assert false
      | s::strs -> List.fold_left Strategies.choice s strs
    end
  | StratConstr ((_, c), b) -> Strategies.one_lemma c b None AllOccurrences
  | StratHints (old, id) -> if old then Strategies.old_hints id else Strategies.hints id
  | StratTerms l -> Strategies.lemmas (List.map (fun (_, c) -> (c, true, None)) l)
  | StratEval r ->
    Strategies.with_env @@ fun env sigma ->
    let sigma, r = r env sigma in
    sigma, Strategies.reduce r
  | StratFold c -> Strategies.fold_glob (fst c)
  | StratVar id -> Id.Map.get id bindings
  | StratFix (id, s) -> Strategies.fix (fun self -> aux (Id.Map.add id self bindings) s)
  | StratMatches p -> Strategies.matches p
  | StratTactic t -> Strategies.ltac1_tactic_call t
  in aux bindings strat


let strategy_of_ast s = strategy_of_ast Id.Map.empty s
