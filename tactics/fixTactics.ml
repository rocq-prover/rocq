(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Context
open Termops
open Environ
open EConstr
open Inductiveops
open Reductionops
open TacticExceptions

let rec mk_holes env sigma = function
| [] -> (sigma, [])
| arg :: rem ->
  let (sigma, arg) = Evarutil.new_evar env sigma arg in
  let (sigma, rem) = mk_holes env sigma rem in
  (sigma, arg :: rem)

let rec check_mutind env sigma k cl = match EConstr.kind sigma (strip_outer_cast sigma cl) with
| Prod (na, c1, b) ->
  if Int.equal k 1 then
    try ignore (find_inductive env sigma c1)
    with Not_found -> Loc.raise FixpointOnNonInductiveType
  else
    let open Context.Rel.Declaration in
    check_mutind (push_rel (LocalAssum (na, c1)) env) sigma (pred k) b
| LetIn (na, c1, t, b) ->
    let open Context.Rel.Declaration in
    check_mutind (push_rel (LocalDef (na, c1, t)) env) sigma k b
| _ -> Loc.raise NotEnoughProducts

let mutual_fix f n others = Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.project gl in
  let concl = Proofview.Goal.concl gl in
  let () = check_mutind env sigma n concl in
  let all = (f, n, concl) :: others in
  let all = List.map (fun (f, n, ar) ->
      let r = Retyping.relevance_of_type env sigma ar in
      (f, r, n, ar))
      all
  in
  let rec mk_sign sign = function
  | [] -> sign
  | (f, r, n, ar) :: oth ->
    let open Context.Named.Declaration in
    let ()  = check_mutind env sigma n ar in
    if mem_named_context_val f sign then
      Loc.raise (IntroAlreadyDeclared f);
    mk_sign (push_named_context_val (LocalAssum (make_annot f r, ar)) sign) oth
  in
  let nenv = reset_with_named_context (mk_sign (named_context_val env) all) env in
  Refine.refine ~typecheck:false begin fun sigma ->
    let (sigma, evs) = mk_holes nenv sigma (List.map (fun (_,_,_,ar) -> ar) all) in
    let ids, rs, _, ars = List.split4 all in
    let evs = List.map (Vars.subst_vars sigma (List.rev ids)) evs in
    let indxs = Array.of_list (List.map (fun n -> n-1) (List.map (fun (_,_,n,_) -> n) all)) in
    let funnames = Array.of_list (List.map2 (fun i r -> make_annot (Name i) r) ids rs) in
    let bodies = Array.of_list evs in
    let typarray = Array.of_list ars in
    let oterm = mkFix ((indxs,0),(funnames,typarray,bodies)) in
    (sigma, oterm)
  end
end

let fix id n = mutual_fix id n []

let rec check_is_mutcoind env sigma cl =
  let b = whd_all env sigma cl in
  match EConstr.kind sigma b with
  | Prod (na, c1, b) ->
    let open Context.Rel.Declaration in
    check_is_mutcoind (push_rel (LocalAssum (na,c1)) env) sigma b
  | _ ->
    try
      let _ = find_coinductive env sigma b in ()
    with Not_found ->
      Loc.raise AllMethodsInCoinductiveType

let mutual_cofix f others = Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.project gl in
  let concl = Proofview.Goal.concl gl in
  let all = (f, concl) :: others in
  List.iter (fun (_, c) -> check_is_mutcoind env sigma c) all;
  let all = List.map (fun (id,t) -> (id, Retyping.relevance_of_type env sigma t, t)) all in
  let rec mk_sign sign = function
  | [] -> sign
  | (f, r, ar) :: oth ->
    let open Context.Named.Declaration in
    if mem_named_context_val f sign then
      Loc.raise (AlreadyUsed f);
    mk_sign (push_named_context_val (LocalAssum (make_annot f r, ar)) sign) oth
  in
  let nenv = reset_with_named_context (mk_sign (named_context_val env) all) env in
  Refine.refine ~typecheck:false begin fun sigma ->
    let (ids, rs, types) = List.split3 all in
    let (sigma, evs) = mk_holes nenv sigma types in
    let evs = List.map (Vars.subst_vars sigma (List.rev ids)) evs in
    (* TODO relevance *)
    let funnames = Array.of_list (List.map2 (fun i r -> make_annot (Name i) r) ids rs) in
    let typarray = Array.of_list types in
    let bodies = Array.of_list evs in
    let oterm = mkCoFix (0, (funnames, typarray, bodies)) in
    (sigma, oterm)
  end
end

let cofix id = mutual_cofix id []
