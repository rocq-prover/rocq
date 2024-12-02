(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Univ
open UVars
open InferCumulativity

let debug = CDebug.create ~name:"UnivVariances" ()

let _variance_opp x =
  let open Variance in
  match x with
  | Invariant -> Invariant
  | Irrelevant -> Irrelevant
  | Covariant -> Contravariant
  | Contravariant -> Covariant

let _global_variances env gr =
  let open Names.GlobRef in
  let open Environ in
  match gr with
  | ConstRef cst ->
    if not (mem_constant cst env) then None
    else let cb = lookup_constant cst env in Declareops.universes_variances cb.const_universes
  | IndRef ind ->
    if not (mem_mind (fst ind) env) then None
    else let mib = lookup_mind (fst ind) env in Declareops.universes_variances mib.mind_universes
  | ConstructRef cstr ->
    if not (mem_mind (fst (fst cstr)) env) then None
    else let mib = lookup_mind (fst (fst cstr)) env in Declareops.universes_variances mib.mind_universes
  | VarRef _id -> None

let _occurrence_of (position, variance) =
  let open Position in
  match position with
  | InBinder i -> { in_binder = Some (i, variance); in_type = None; in_term = None}
  | InType -> { in_binder = None; in_type = Some variance; in_term = None}
  | InTerm -> { in_binder = None; in_type = None; in_term = Some variance}

let compute_variances_constr env ~evars status position cv_pb c =
  let status = Inf.set_position position status in
  try infer_term cv_pb env ~evars status c
  with
  | InferCumulativity.BadVariance (lev, expected, actual) ->
    Type_errors.error_bad_variance env ~lev ~expected ~actual


let compute_variances_constr env sigma status position variance c =
  let status = compute_variances_constr env ~evars:(Evd.evar_handler sigma) status position variance c in
  debug Pp.(fun () -> str"Variances of " ++ (try Termops.Internal.print_constr_env env sigma (EConstr.of_constr c) with _ -> str"<anomaly in printing>") ++ fnl () ++
    InferCumulativity.pr_variances (Evd.pr_level sigma) (InferCumulativity.Inf.inferred status));
  status

let compute_variances env sigma status position variance c =
  let c = EConstr.to_constr ~abort_on_undefined_evars:false sigma c in
  compute_variances_constr env sigma status position variance c

let compute_variances_context_constr env sigma ?(position = fun x -> Position.InBinder x) ?(cumul_pb=InvCumul) status ctx =
  let fold_binder i binder (env, status) =
    let open Context.Rel.Declaration in
    let status = match binder with
    | LocalAssum (na, ty) ->
      compute_variances_constr env sigma status (position i) cumul_pb ty
    | LocalDef _ -> status
    in (Environ.push_rel binder env, status)
  in
  let env, variances = CList.fold_right_i fold_binder 0 ctx (env, status) in
  variances

let compute_variances_context env sigma ?(position = fun x -> Position.InBinder x) ?(cumul_pb=InvCumul) status ctx =
  let fold_binder i binder (env, status) =
    let open Context.Rel.Declaration in
    let status = match binder with
    | LocalAssum (na, ty) -> compute_variances env sigma status (position i) cumul_pb ty
    | LocalDef _ -> status
    in (EConstr.push_rel binder env, status)
  in
  let env, variances = CList.fold_right_i fold_binder 0 ctx (env, status) in
  debug Pp.(fun () -> str"Variances in context: " ++ Inf.pr (Evd.pr_level sigma) variances);
  variances

let compute_variances_body_constr env sigma status c =
  let ctx, c = Term.decompose_lambda_decls c in
  let status = compute_variances_context_constr env sigma status (Vars.smash_rel_context ctx) in
  compute_variances_constr (Environ.push_rel_context ctx env) sigma status InTerm Cumul c

let compute_variances_body env sigma status c =
  compute_variances_body_constr env sigma status (EConstr.to_constr ~abort_on_undefined_evars:false sigma c)

let compute_variances_type_constr env sigma ?(position=Position.InType) ?(ctx_position = fun x -> Position.InBinder x) ?(ctx_cumul_pb=InvCumul) status c =
  let ctx, c = Term.decompose_prod_decls c in
  let status = compute_variances_context_constr env sigma ~position:ctx_position ~cumul_pb:ctx_cumul_pb status (Vars.smash_rel_context ctx) in
  compute_variances_constr (Environ.push_rel_context ctx env) sigma status position Cumul c

let compute_variances_type env sigma ?(position=Position.InType) ?(ctx_position = fun x -> Position.InBinder x) ?(ctx_cumul_pb=InvCumul) status c =
  compute_variances_type_constr env sigma status ~position ~ctx_position ~ctx_cumul_pb
    (EConstr.to_constr ~abort_on_undefined_evars:false sigma c)

let init_status ?(position=Position.InType) ?(udecl : UState.universe_decl option) sigma =
  let ustate = Evd.ustate sigma in
  let ctx = UState.context_set ustate in
  match udecl with
  | None -> Inf.start_inference (ContextSet.levels ctx) position
  | Some udecl ->
    let levels = ContextSet.levels ctx in
    let us = udecl.UState.univdecl_instance and variances = udecl.UState.univdecl_variances in
    match variances with
    | None -> Inf.start_inference levels position
    | Some vs ->
      assert (Int.equal (Array.length vs) (List.length us));
      let comp = CList.combine us (Array.to_list vs) in
      let map = Level.Set.fold (fun l m ->
        try
          let open InferCumulativity in
          let (_, v) = List.find (fun (l', _) -> Level.equal l l') comp in
          (match v with
          | None -> Level.Map.add l (Infer, default_occ) m
          | Some v -> Level.Map.add l (Check, make_occ v UVars.Position.InType) m)
        with Not_found -> Level.Map.add l (Infer, default_occ) m)
        levels Level.Map.empty
      in Inf.start_map map position

let universe_variances_body_ty env sigma status ?typ body =
  let status = Option.fold_left (compute_variances_type env sigma) status typ in
  let variances = compute_variances_body env sigma status body in
  debug Pp.(fun () -> Inf.pr (Evd.pr_level sigma) variances ++ fnl () ++
    str "Computed from body " ++ Termops.Internal.print_constr_env env sigma body ++ fnl () ++
    str " and type: " ++ Option.cata (Termops.Internal.print_constr_env env sigma) (mt()) typ);
  Inf.inferred variances

let universe_variances env sigma ?typ body =
  let status = init_status ~position:InTerm sigma in
  universe_variances_body_ty env sigma status ?typ body

let universe_variances_constr env sigma ?typ body =
  let status = init_status sigma in
  let status = Option.fold_left (compute_variances_type_constr env sigma) status typ in
  let status = compute_variances_body_constr env sigma status body in
  Inf.inferred status

let universe_variances_of_type env sigma typ =
  let status = init_status sigma in
  let status = compute_variances_type env sigma status typ in
  debug Pp.(fun () -> Inf.pr (Evd.pr_level sigma) status ++ fnl () ++
    str "Computed from type " ++ Termops.Internal.print_constr_env env sigma typ);
  Inf.inferred status

let universe_variances_of_inductive env sigma ~udecl ~params ~arities ~constructors =
  let status = init_status ~udecl sigma in
  let params = EConstr.Vars.smash_rel_context params in
  let status = compute_variances_context env sigma status params in
  let paramlen = Context.Rel.length params in
  let status = List.fold_left (compute_variances_type ~ctx_position:(fun i -> InBinder (i + paramlen)) env sigma) status arities in
  let status = List.fold_left (fun status (_nas, tys) ->
    List.fold_left (fun status ty ->
      compute_variances_type env sigma status ~position:InTerm ~ctx_position:(fun _ -> InTerm) ~ctx_cumul_pb:Cumul ty) status tys) status constructors in
    Inf.inferred status

let universe_variances_of_record env sigma ~env_ar_pars ~params ~fields ~types =
  let status = init_status sigma in
  let status = compute_variances_context env sigma status params in
  let paramlen = Context.Rel.length params in
  let status = List.fold_left (compute_variances_type ~ctx_position:(fun i -> InBinder (i + paramlen)) env sigma) status types in
  let status = List.fold_left (compute_variances_context env_ar_pars sigma ~position:(fun _ -> InTerm) ~cumul_pb:Cumul) status fields in
  Inf.inferred status

let universe_variances_of_fix env sigma types bodies =
  let status = init_status sigma in
  let status = List.fold_left2 (fun status typ body ->
    let status = compute_variances_type env sigma status typ in
    Option.fold_left (compute_variances_body env sigma) status body) status types bodies in
  Inf.inferred status

let universe_variances_of_proofs env sigma proofs =
  let status = init_status sigma in
  let status = List.fold_left (fun status (body, typ) ->
    let status = compute_variances_body_constr env sigma status body in
    compute_variances_type_constr env sigma status typ) status proofs in
  Inf.inferred status

let universe_variances_of_proof_statements env sigma proofs =
  let status = init_status sigma in
  let status = List.fold_left (fun status typ ->
    compute_variances_type env sigma status typ) status proofs in
  Inf.inferred status

let universe_variances_of_partial_proofs env sigma proofs =
  let status = init_status sigma in
  let status = List.fold_left (fun status body ->
    compute_variances_body env sigma status body) status proofs in
  Inf.inferred status

let universe_variances_of_named_context env sigma ~as_types ?(cumul_pb=InvCumul) ctx =
  let status = init_status sigma in
  let fold_binder i binder status =
    let open Context.Named.Declaration in
    if as_types then
      let status = compute_variances_type env sigma status (get_type binder) in
      Option.fold_left (compute_variances_body env sigma) status (get_value binder)
    else let status = compute_variances env sigma status (InBinder i) cumul_pb (get_type binder) in
    Option.cata (compute_variances env sigma status (InBinder i) cumul_pb) status (get_value binder)
  in
  let variances = CList.fold_right_i fold_binder 0 ctx status in
  debug Pp.(fun () -> str"Variances in named context: " ++ Inf.pr (Evd.pr_level sigma) variances);
  Inf.inferred variances
