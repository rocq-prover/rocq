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
open CErrors
open Names
open Constr
open Environ
open EConstr
open Vars
open Reductionops
open Evd
open Tacred
open Genredexpr
open Logic
open Locus
open Proofview.Notations
open TacticExceptions

module NamedDecl = Context.Named.Declaration

(**************************************************************)
(** Basic conversion tactics.                                 *)
(**************************************************************)

let convert ?(pb = Conversion.CONV) x y =
  Proofview.Goal.enter begin fun gl ->
    match Tacmach.pf_apply (Reductionops.infer_conv ~pb) gl x y with
    | Some sigma -> Proofview.Unsafe.tclEVARS sigma
    | None -> Loc.raise NotConvertible
    | exception e when CErrors.noncritical e ->
      let _, info = Exninfo.capture e in
      (* FIXME: Sometimes an anomaly is raised from conversion *)
      Loc.raise ?loc:(Loc.get_loc info) NotConvertible
  end

(* Not sure if being able to disable [cast] is useful. Uses seem picked somewhat randomly. *)
let convert_concl ~cast ~check ty k =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let conclty = Proofview.Goal.concl gl in
    Refine.refine_with_principal ~typecheck:false begin fun sigma ->
      let sigma =
        if check then begin
          let sigma, _ = Typing.type_of env sigma ty in
          match Reductionops.infer_conv env sigma ty conclty with
          | None -> Loc.raise NotConvertible
          | Some sigma -> sigma
        end else sigma
      in
      let (sigma, x) = Evarutil.new_evar env sigma ty in
      let ans = if not cast then x else mkCast(x,k,conclty) in
      (sigma, ans, Some (fst @@ destEvar sigma x))
    end
  end

let convert_hyp ~check ~reorder d =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.project gl in
    let ty = Proofview.Goal.concl gl in
    let sign = convert_hyp ~check ~reorder env sigma d in
    let env = reset_with_named_context sign env in
    Refine.refine_with_principal ~typecheck:false begin fun sigma ->
      let sigma, ev = Evarutil.new_evar env sigma ty in
      sigma, ev, Some (fst @@ destEvar sigma ev)
    end
  end

(**************************************************************)
(** Reduction tactics.                                        *)
(**************************************************************)

type tactic_reduction = Reductionops.reduction_function
type e_tactic_reduction = Reductionops.e_reduction_function

let[@ocaml.inline] (let*) m f = match m with
| NoChange -> NoChange
| Changed v -> f v

let e_pf_change_decl (redfun : bool -> Tacred.change_function) where env sigma decl =
  let open Context.Named.Declaration in
  match decl with
  | LocalAssum (id,ty) ->
    let () =
      if where == InHypValueOnly then Loc.raise (VariableHasNoValue id.binder_name)
    in
    let* (sigma, ty') = redfun false env sigma ty in
    Changed (sigma, LocalAssum (id, ty'))
  | LocalDef (id,b,ty) ->
    let (sigma, b') =
      if where != InHypTypeOnly then match redfun true env sigma b with
      | NoChange -> (sigma, NoChange)
      | Changed (sigma, b') -> (sigma, Changed b')
      else (sigma, NoChange)
    in
    let (sigma, ty') =
      if where != InHypValueOnly then match redfun false env sigma ty with
      | NoChange -> (sigma, NoChange)
      | Changed (sigma, ty') -> (sigma, Changed ty')
      else (sigma, NoChange)
    in
    match b', ty' with
    | NoChange, NoChange -> NoChange
    | Changed b', NoChange -> Changed (sigma, LocalDef (id, b', ty))
    | NoChange, Changed ty' -> Changed (sigma, LocalDef (id, b, ty'))
    | Changed b', Changed ty' -> Changed (sigma, LocalDef (id, b', ty'))

let bind_change_occurrences occs = function
  | None -> None
  | Some c -> Some (Redexpr.out_with_occurrences (occs,c))

(* The following two tactics apply an arbitrary
   reduction function either to the conclusion or to a
   certain hypothesis *)

(** Tactic reduction modulo evars (for universes essentially) *)

let e_change_in_concl ~cast ~check (redfun, sty) =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    match redfun (Tacmach.pf_env gl) sigma (Tacmach.pf_concl gl) with
    | NoChange -> Proofview.tclUNIT ()
    | Changed (sigma, c') ->
      Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
      (convert_concl ~cast ~check c' sty)
  end

let e_change_in_hyp ~check ~reorder redfun (id,where) =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let hyp = Tacmach.pf_get_hyp id gl in
    match e_pf_change_decl redfun where (Proofview.Goal.env gl) sigma hyp with
    | NoChange -> Proofview.tclUNIT ()
    | Changed (sigma, c) ->
      Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
      (convert_hyp ~check ~reorder c)
  end

let e_change_option ~check ~reorder (redfun, sty) = function
| None ->
  e_change_in_concl ~cast:true ~check (redfun, sty)
| Some id ->
  let redfun _ env sigma c = redfun env sigma c in
  e_change_in_hyp ~check ~reorder redfun id

type hyp_conversion =
| AnyHypConv (** Arbitrary conversion *)
| StableHypConv (** Does not introduce new dependencies on variables *)
| LocalHypConv (** Same as above plus no dependence on the named environment *)

let e_change_in_hyps ~check ~reorder f args = match args with
| [] -> Proofview.tclUNIT ()
| _ :: _ ->
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.project gl in
    let (env, sigma) = match reorder with
    | LocalHypConv ->
      (* If the reduction function is known not to depend on the named
          context, then we can perform it in parallel. *)
      let fold accu arg =
        let (id, redfun) = f arg in
        let old = try Id.Map.find id accu with Not_found -> [] in
        Id.Map.add id (redfun :: old) accu
      in
      let reds = List.fold_left fold Id.Map.empty args in
      let evdref = ref sigma in
      let map d =
        let id = NamedDecl.get_id d in
        match Id.Map.find id reds with
        | reds ->
          let d = EConstr.of_named_decl d in
          let fold redfun (sigma, d) = match redfun env sigma d with
          | NoChange -> sigma, d
          | Changed (sigma, d) -> sigma, d
          in
          let (sigma, d) = List.fold_right fold reds (sigma, d) in
          let () = evdref := sigma in
          EConstr.Unsafe.to_named_decl d
        | exception Not_found -> d
      in
      let sign = Environ.map_named_val map (Environ.named_context_val env) in
      let env = reset_with_named_context sign env in
      (env, !evdref)
    | StableHypConv | AnyHypConv ->
      let reorder = reorder == AnyHypConv in
      let fold (env, sigma) arg =
        let (id, redfun) = f arg in
        let hyp =
          try lookup_named id env
          with Not_found ->
            raise (RefinerError (env, sigma, NoSuchHyp id))
        in
        match redfun env sigma hyp with
        | NoChange -> (env, sigma)
        | Changed (sigma, d) ->
          let sign = Logic.convert_hyp ~check ~reorder env sigma d in
          let env = reset_with_named_context sign env in
          (env, sigma)
      in
      List.fold_left fold (env, sigma) args
    in
    let ty = Proofview.Goal.concl gl in
    Proofview.Unsafe.tclEVARS sigma
    <*>
    Refine.refine_with_principal ~typecheck:false begin fun sigma ->
      let sigma, ev = Evarutil.new_evar env sigma ty in
      sigma, ev, Some (fst @@ destEvar sigma ev)
    end
  end

let e_reduct_in_concl ~cast ~check (redfun, sty) =
  let redfun env sigma c = Changed (redfun env sigma c) in
  e_change_in_concl ~cast ~check (redfun, sty)

let reduct_in_concl ~cast ~check (redfun, sty) =
  let redfun env sigma c = Changed (sigma, redfun env sigma c) in
  e_change_in_concl ~cast ~check (redfun, sty)

let e_reduct_in_hyp ~check ~reorder redfun (id, where) =
  let redfun _ env sigma c = Changed (redfun env sigma c) in
  e_change_in_hyp ~check ~reorder redfun (id, where)

let reduct_in_hyp ~check ~reorder redfun (id, where) =
  let redfun _ env sigma c = Changed (sigma, redfun env sigma c) in
  e_change_in_hyp ~check ~reorder redfun (id, where)

let e_reduct_option ~check redfun = function
  | Some id -> e_reduct_in_hyp ~check ~reorder:check (fst redfun) id
  | None    -> e_reduct_in_concl ~cast:true ~check redfun

let reduct_option ~check (redfun, sty) where =
  let redfun env sigma c = (sigma, redfun env sigma c) in
  e_reduct_option ~check (redfun, sty) where

type change_arg = Ltac_pretype.patvar_map -> env -> evar_map -> (evar_map * EConstr.constr) Tacred.change

let make_change_arg c pats env sigma =
  Changed (sigma, replace_vars sigma (Id.Map.bindings pats) c) (* TODO: fast-path *)

let is_partial_template_head env sigma c =
  let (hd, args) = decompose_app sigma c in
  match destRef sigma hd with
  | (ConstructRef (ind, _) | IndRef ind), _ ->
    let (mib, _) = Inductive.lookup_mind_specif env ind in
    begin match mib.mind_template with
    | None -> false
    | Some _ -> Array.length args < mib.mind_nparams
    end
  | (VarRef _ | ConstRef _), _ -> false
  | exception DestKO -> false

let check_types env sigma mayneedglobalcheck deep newc origc =
  let t1 = Retyping.get_type_of env sigma newc in
  if deep then begin
    let () =
      (* When changing a partially applied template term in a context, one must
         be careful to resynthetize the constraints as the implicit levels from
         the arguments are not written in the term. *)
      if is_partial_template_head env sigma newc ||
        is_partial_template_head env sigma origc then
        mayneedglobalcheck := true
    in
    let t2 = Retyping.get_type_of env sigma origc in
    let sigma, t2 = Evarsolve.refresh_universes
                      ~onlyalg:true (Some false) env sigma t2 in
    match infer_conv ~pb:Conversion.CUMUL env sigma t1 t2 with
    | None ->
      if
        isSort sigma (whd_all env sigma t1) &&
        isSort sigma (whd_all env sigma t2)
      then (mayneedglobalcheck := true; sigma)
      else
        Loc.raise (ConvertIncompatibleTypes (env,sigma,t2,t1))
    | Some sigma -> sigma
  end
  else
    if not (isSort sigma (whd_all env sigma t1)) then
      Loc.raise ConvertNotAType
    else sigma

(* Now we introduce different instances of the previous tacticals *)
let change_and_check cv_pb mayneedglobalcheck deep t env sigma c = match t env sigma with
| NoChange -> NoChange
| Changed (sigma, t') ->
  let sigma = check_types env sigma mayneedglobalcheck deep t' c in
  match infer_conv ~pb:cv_pb env sigma t' c with
  | None -> Loc.raise NotConvertible
  | Some sigma -> Changed (sigma, t')

(* Use cumulativity only if changing the conclusion not a subterm *)
let change_on_subterm ~check cv_pb deep t where env sigma c =
  let mayneedglobalcheck = ref false in
  let ans = match where with
  | None ->
      if check then
        change_and_check cv_pb mayneedglobalcheck deep (t Id.Map.empty) env sigma c
      else
        t Id.Map.empty env sigma
  | Some occl ->
      e_contextually false occl
        (fun subst ->
          if check then
            change_and_check Conversion.CONV mayneedglobalcheck true (t subst)
          else
            fun env sigma _c -> t subst env sigma) env sigma c in
  match ans with
  | NoChange -> NoChange
  | Changed (sigma, c) ->
    let sigma = if !mayneedglobalcheck then
      begin
        try fst (Typing.type_of env sigma c)
        with e when noncritical e ->
          Loc.raise (ReplacementIllTyped e)
      end else sigma
    in
    Changed (sigma, c)

let change_in_concl ~check occl t =
  (* No need to check in e_change_in_concl, the check is done in change_on_subterm *)
  e_change_in_concl ~cast:false ~check:false
    ((change_on_subterm ~check Conversion.CUMUL false t occl),DEFAULTcast)

let change_in_hyp ~check occl t id  =
  (* Same as above *)
  e_change_in_hyp ~check:false ~reorder:check (fun x -> change_on_subterm ~check Conversion.CONV x t occl) id

let concrete_clause_of enum_hyps cl = match cl.onhyps with
| None ->
  let f id = (id, AllOccurrences, InHyp) in
  List.map f (enum_hyps ())
| Some l ->
  List.map (fun ((occs, id), w) -> (id, occs, w)) l

let change ~check chg c cls =
  Proofview.Goal.enter begin fun gl ->
    let hyps = concrete_clause_of (fun () -> Tacmach.pf_ids_of_hyps gl) cls in
    begin match cls.concl_occs with
    | NoOccurrences -> Proofview.tclUNIT ()
    | occs -> change_in_concl ~check (bind_change_occurrences occs chg) c
    end
    <*>
    let f (id, occs, where) =
      let occl = bind_change_occurrences occs chg in
      let redfun deep env sigma t = change_on_subterm ~check Conversion.CONV deep c occl env sigma t in
      let redfun env sigma d = e_pf_change_decl redfun where env sigma d in
      (id, redfun)
    in
    let reorder = if check then AnyHypConv else StableHypConv in
    (* Don't check, we do it already in [change_on_subterm]. *)
    e_change_in_hyps ~check:false ~reorder f hyps
  end

let change_concl t =
  change_in_concl ~check:true None (make_change_arg t)

let red_product_exn env sigma c = match red_product env sigma c with
| None -> user_err Pp.(str "No head constant to reduce.")
| Some c -> c

let red = reduct_option ~check:false (red_product_exn, DEFAULTcast)

let hnf = reduct_option ~check:false (hnf_constr, DEFAULTcast)

let simpl = reduct_option ~check:false (simpl, DEFAULTcast)

let normalise = reduct_option ~check:false (compute, DEFAULTcast)

let normalise_vm_in_concl = reduct_in_concl ~cast:true ~check:false (Redexpr.cbv_vm, VMcast)

let unfold loccname = reduct_option ~check:false (unfoldn loccname, DEFAULTcast)

let pattern l = e_change_option ~check:false ~reorder:false (pattern_occs l, DEFAULTcast)

(* The main reduction function *)

let is_local_flag env flags =
  if flags.rDelta then false
  else
    let check = function
    | Evaluable.EvalVarRef _ -> false
    | Evaluable.EvalConstRef c -> Id.Set.is_empty (Environ.vars_of_global env (GlobRef.ConstRef c))
    | Evaluable.EvalProjectionRef c -> false (* FIXME *)
    in
    List.for_all check flags.rConst

let is_local_unfold env flags =
  let check (_, c) = match c with
  | Evaluable.EvalVarRef _ -> false
  | Evaluable.EvalConstRef c -> Id.Set.is_empty (Environ.vars_of_global env (GlobRef.ConstRef c))
  | Evaluable.EvalProjectionRef c -> false (* FIXME *)
  in
  List.for_all check flags

let change_of_red_expr_val ?occs redexp =
  let (redfun, kind) = Redexpr.reduction_of_red_expr_val ?occs redexp in
  let redfun env sigma c = Changed (redfun env sigma c) in (* TODO: fast-path *)
  (redfun, kind)

let reduce redexp cl =
  let trace env sigma =
    let open Printer in
    let pr = ((fun e -> pr_econstr_env e), (fun e -> pr_leconstr_env e), pr_evaluable_reference, pr_constr_pattern_env, int) in
    Pp.(hov 2 (Ppred.pr_red_expr_env env sigma pr str redexp))
  in
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let hyps = concrete_clause_of (fun () -> Tacmach.pf_ids_of_hyps gl) cl in
  let nbcl = (if cl.concl_occs = NoOccurrences then 0 else 1) + List.length hyps in
  let check = match redexp with Fold _ | Pattern _ -> true | _ -> false in
  let reorder = match redexp with
  | Fold _ | Pattern _ -> AnyHypConv
  | Simpl (flags, _) | Cbv flags | Cbn flags | Lazy flags ->
    if is_local_flag env flags then LocalHypConv else StableHypConv
  | Unfold flags ->
    if is_local_unfold env flags then LocalHypConv else StableHypConv
  | Red | Hnf | CbvVm _ | CbvNative _ -> StableHypConv
  | ExtraRedExpr _ -> StableHypConv (* Should we be that lenient ?*)
  in
  let redexp = Redexpr.eval_red_expr env redexp in
  Proofview.Trace.name_tactic (fun () -> trace env sigma) begin
  begin match cl.concl_occs with
  | NoOccurrences -> Proofview.tclUNIT ()
  | occs ->
    let occs = Redexpr.out_occurrences occs in
    let redfun = change_of_red_expr_val ~occs:(occs, nbcl) redexp in
    e_change_in_concl ~cast:true ~check redfun
  end
  <*>
  let f (id, occs, where) =
    let occs = Redexpr.out_occurrences occs in
    let (redfun, _) = change_of_red_expr_val ~occs:(occs, nbcl) redexp in
    let redfun _ env sigma c = redfun env sigma c in
    let redfun env sigma d = e_pf_change_decl redfun where env sigma d in
    (id, redfun)
  in
  e_change_in_hyps ~check ~reorder f hyps
  end
  end
