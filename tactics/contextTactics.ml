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
open Util
open Names
open Termops
open Environ
open EConstr
open Logic
open Evarutil
open Proofview.Notations
open TacticExceptions

module NamedDecl = Context.Named.Declaration

(**************************************************************)
(** Clear a hypothesis.                                       *)
(**************************************************************)

let error_clear_dependency env sigma id err inglobal =
  Loc.raise (ClearDependency (env, sigma, Some id, err, inglobal))

let clear ?(fail = error_clear_dependency) = function
  | [] -> Proofview.tclUNIT ()
  | ids ->
  Proofview.Goal.enter begin fun gl ->
    let ids = List.fold_right Id.Set.add ids Id.Set.empty in
    (* clear_hyps_in_evi does not require nf terms *)
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.project gl in
    let concl = Proofview.Goal.concl gl in
    let (sigma, hyps, concl) =
      try clear_hyps_in_evi env sigma (named_context_val env) concl ids
      with Evarutil.ClearDependencyError (id,err,inglobal) -> fail env sigma id err inglobal
    in
    let env = reset_with_named_context hyps env in
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
    (Refine.refine_with_principal ~typecheck:false begin fun sigma ->
      let sigma, ev = Evarutil.new_evar env sigma concl in
      sigma, ev, Some (fst @@ destEvar sigma ev)
    end)
  end

let clear_wildcards ids =
  let clear_wildcards_msg ?loc env sigma _id err inglobal =
    user_err ?loc (clear_dependency_msg env sigma None err inglobal)
  in
  Tacticals.tclMAP (fun {CAst.loc;v=id} -> clear ~fail:(clear_wildcards_msg ?loc) [id]) ids

(**************************************************************)
(** Clear the body of a hypothesis.                           *)
(**************************************************************)

let check_is_type env sigma idl ids ty =
  try
    let sigma, _ = Typing.sort_of env sigma ty in
    sigma
  with e when CErrors.noncritical e ->
    raise (DependsOnBody (idl, ids, None))

let check_decl env sigma idl ids decl =
  let open Context.Named.Declaration in
  let ty = NamedDecl.get_type decl in
  try
    let sigma, _ = Typing.sort_of env sigma ty in
    let sigma = match decl with
    | LocalAssum _ -> sigma
    | LocalDef (_,c,_) -> Typing.check env sigma c ty
    in
    sigma
  with e when CErrors.noncritical e ->
    let id = NamedDecl.get_id decl in
    raise (DependsOnBody (idl, ids, Some id))

let clear_body idl =
  let open Context.Named.Declaration in
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let concl = Proofview.Goal.concl gl in
    let sigma = Tacmach.project gl in
    let ctx = named_context env in
    let ids = Id.Set.of_list idl in
    (* We assume the context to respect dependencies *)
    let rec fold ids ctx =
      if Id.Set.is_empty ids then
        let base_env = reset_context env in
        let env = push_named_context ctx base_env in
        env, sigma, Id.Set.empty
      else
        match ctx with
        | [] -> assert false
        | decl :: ctx ->
          let decl, ids, found =
            match decl with
            | LocalAssum (id,t) ->
              let () =
                if Id.Set.mem id.binder_name ids then
                  Loc.raise (VariableHasNoValue id.binder_name)
              in
              decl, ids, false
            | LocalDef (id,_,t) as decl ->
               if Id.Set.mem id.binder_name ids
               then LocalAssum (id, t), Id.Set.remove id.binder_name ids, true
               else decl, ids, false
          in
          let env, sigma, ids = fold ids ctx in
          if Id.Set.exists (fun id -> occur_var_in_decl env sigma id decl) ids then
            let sigma = check_decl env sigma idl ids decl in (* can sigma really change? *)
            let ids = Id.Set.add (get_id decl) ids in
            push_named decl env, sigma, Id.Set.add (get_id decl) ids
          else
            push_named decl env, sigma, if found then Id.Set.add (get_id decl) ids else ids
    in
    try
      let env, sigma, ids = fold ids ctx in
      let sigma =
        if Id.Set.exists (fun id -> occur_var env sigma id concl) ids then
          check_is_type env sigma idl ids concl
        else sigma
      in
      Proofview.Unsafe.tclEVARS sigma <*>
    Refine.refine_with_principal ~typecheck:false begin fun sigma ->
      let sigma, ev = Evarutil.new_evar env sigma concl in
      sigma, ev, Some (fst @@ destEvar sigma ev)
    end
    with DependsOnBody _ as exn ->
      let _, info = Exninfo.capture exn in
      Proofview.tclZERO ~info exn
    end

(**************************************************************)
(** Clear all but a few hypotheses.                           *)
(**************************************************************)

let keep hyps =
  Proofview.Goal.enter begin fun gl ->
  Proofview.tclENV >>= fun env ->
  let ccl = Proofview.Goal.concl gl in
  let sigma = Tacmach.project gl in
  let cl, _ =
    fold_named_context_reverse (fun (clear,keep) decl ->
      let decl = EConstr.of_named_decl decl in
      let hyp = NamedDecl.get_id decl in
      if Id.List.mem hyp hyps
        || List.exists (occur_var_in_decl env sigma hyp) keep
        || occur_var env sigma hyp ccl
      then (clear,decl::keep)
      else (hyp::clear,keep))
      ~init:([],[]) (Proofview.Goal.env gl)
  in
  clear cl
  end

(**************************************************************)
(** Move hypotheses.                                          *)
(**************************************************************)

let move_hyp id dest =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.project gl in
    let ty = Proofview.Goal.concl gl in
    let sign = named_context_val env in
    let sign' = move_hyp_in_named_context env sigma id dest sign in
    let env = reset_with_named_context sign' env in
    Refine.refine_with_principal ~typecheck:false begin fun sigma ->
      let sigma, ev = Evarutil.new_evar env sigma ty in
      sigma, ev, Some (fst @@ destEvar sigma ev)
    end
  end

(**************************************************************)
(** Rename hypotheses.                                        *)
(**************************************************************)

let rename_hyp repl =
  let fold accu (src, dst) = match accu with
  | None -> None
  | Some (srcs, dsts) ->
    if Id.Set.mem src srcs then None
    else if Id.Set.mem dst dsts then None
    else
      let srcs = Id.Set.add src srcs in
      let dsts = Id.Set.add dst dsts in
      Some (srcs, dsts)
  in
  let init = Some (Id.Set.empty, Id.Set.empty) in
  let dom = List.fold_left fold init repl in
  match dom with
  | None ->
    let info = Exninfo.reify () in
    Tacticals.tclZEROMSG ~info (str "Not a one-to-one name mapping")
  | Some (src, dst) ->
    Proofview.Goal.enter begin fun gl ->
      let concl = Proofview.Goal.concl gl in
      let env = Proofview.Goal.env gl in
      let sign = named_context_val env in
      let sigma = Proofview.Goal.sigma gl in
      let relevance = Proofview.Goal.relevance gl in
      (* Check that we do not mess variables *)
      let vars = ids_of_named_context_val sign in
      let () =
        if not (Id.Set.subset src vars) then
          let hyp = Id.Set.choose (Id.Set.diff src vars) in
          raise (RefinerError (env, sigma, NoSuchHyp hyp))
      in
      let mods = Id.Set.diff vars src in
      let () =
        try
          let elt = Id.Set.choose (Id.Set.inter dst mods) in
          Loc.raise (AlreadyUsed elt)
        with Not_found -> ()
      in
      (* All is well *)
      let make_subst (src, dst) = (src, mkVar dst) in
      let subst = List.map make_subst repl in
      let subst c = Vars.replace_vars sigma subst c in
      let replace id = try List.assoc_f Id.equal id repl with Not_found -> id in
      let map decl = decl |> NamedDecl.map_id replace |> NamedDecl.map_constr subst in
      let ohyps = named_context_of_val sign in
      let nhyps = List.map map ohyps in
      let nconcl = subst concl in
      let nctx = val_of_named_context nhyps in
      let fold odecl ndecl accu =
        if Id.equal (NamedDecl.get_id odecl) (NamedDecl.get_id ndecl) then
          SList.default accu
        else
          SList.cons (mkVar @@ NamedDecl.get_id odecl) accu
      in
      let instance = List.fold_right2 fold ohyps nhyps SList.empty in
      Refine.refine_with_principal ~typecheck:false begin fun sigma ->
        let sigma, ev = Evarutil.new_pure_evar nctx sigma ~relevance nconcl in
        sigma, mkEvar (ev, instance), Some ev
      end
    end
