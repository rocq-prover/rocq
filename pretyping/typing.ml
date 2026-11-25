(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module CVars = Vars

open CErrors
open Util
open Constr
open Context
open Environ
open EConstr
open Vars
open Reductionops
open Inductive
open Inductiveops
open Arguments_renaming
open Pretype_errors
open Context.Rel.Declaration

module GR = Names.GlobRef

let fresh_template_context env0 sigma ind (mib, _ as spec) ?(refresh_all=false) args =
  let template = Option.get mib.Declarations.mind_template in
  let templ = Array.of_list template.template_param_arguments in
  let ctx = CVars.subst_instance_context template.template_defaults mib.Declarations.mind_params_ctxt in
  let ctx = List.rev (EConstr.of_rel_context ctx) in
  let rec freshen i env sigma accu sorts = function
  | [] -> sigma, List.rev sorts
  | LocalAssum (na, t) as decl :: ctx ->
    let sigma, decl, s =
      match templ.(i) with
      | Some _ ->
        let decls, s0 = Reductionops.dest_arity env sigma t in
        let sigma, s =
          if i < Array.length args then match Reductionops.sort_of_arity env sigma args.(i).uj_type with
          | s -> sigma, s
          | exception Reduction.NotArity -> Evd.new_sort_variable Evd.univ_flexible sigma
          else if refresh_all then Evd.new_sort_variable Evd.univ_flexible sigma
          else sigma, s0
        in
        let t = EConstr.it_mkProd_or_LetIn (mkSort s) decls in
        let s ~default = match ESorts.kind sigma s with
        | Sorts.SProp ->
          let indty = EConstr.of_constr @@
            Inductive.type_of_inductive (spec, UVars.Instance.empty)
          in
          error_cant_apply_bad_type env0 sigma
            (i+1, mkSort (ESorts.make default), args.(i).uj_type)
            (make_judge (mkIndU (ind, EInstance.empty)) indty)
            args
        | Sorts.Prop -> TemplateProp
        | Sorts.Set -> TemplateUniv Univ.Universe.type0
        | Sorts.Type u | Sorts.GSort (_, u) | Sorts.VSort (_, u) -> TemplateUniv u
        in
        sigma, LocalAssum (na, t), s
      | None ->
        sigma, decl, (fun ~default -> assert false)
    in
    freshen (i + 1) (push_rel decl env) sigma (decl :: accu) (s :: sorts) ctx
  | LocalDef (na, b, t) as decl :: ctx ->
    freshen i (push_rel decl env) sigma (decl :: accu) sorts ctx
  in
  freshen 0 env0 sigma [] [] ctx

let get_template_parameters env sigma ind ?refresh_all args =
  let spec = Inductive.lookup_mind_specif env ind in
  fresh_template_context env sigma ind spec ?refresh_all args

let type_judgment env sigma j =
  match EConstr.kind sigma (whd_all env sigma j.uj_type) with
    | Sort s -> sigma, {utj_val = j.uj_val; utj_type = s }
    | Evar ev ->
        let (sigma,s) = Evardefine.define_evar_as_sort env sigma ev in
        sigma, { utj_val = j.uj_val; utj_type = s }
    | _ -> error_not_a_type env sigma j

let assumption_of_judgment env sigma j =
  try
    let sigma, j = type_judgment env sigma j in
    sigma, j.utj_val
  with Type_errors.TypeError _ | PretypeError _ ->
    error_assumption env sigma j

let judge_of_apply_core env sigma funj argjv =
  let rec apply_rec sigma n subs typ = function
  | [] ->
    let typ = Vars.esubst Vars.lift_substituend subs typ in
    sigma, { uj_val  = mkApp (j_val funj, Array.map j_val argjv);
             uj_type = typ }
  | hj::restjl ->
    let sigma, c1, subs, c2 = match EConstr.kind sigma typ with
    | Prod (_, c1, c2) ->
      (* Fast path *)
      let c1 = Vars.esubst Vars.lift_substituend subs c1 in
      let subs = Esubst.subs_cons (Vars.make_substituend hj.uj_val) subs in
      sigma, c1, subs, c2
    | _ ->
      let typ = Vars.esubst Vars.lift_substituend subs typ in
      let subs = Esubst.subs_cons (Vars.make_substituend hj.uj_val) (Esubst.subs_id 0) in
      match EConstr.kind sigma (whd_all env sigma typ) with
      | Prod (_, c1, c2) -> sigma, c1, subs, c2
      | Evar ev ->
        let (sigma,t) = Evardefine.define_evar_as_product env sigma ev in
        let (_, c1, c2) = destProd sigma t in
        sigma, c1, subs, c2
      | _ ->
        let seen, rest = Array.chop (n-1) argjv in
        error_cant_apply_not_functional env sigma
          (make_judge (mkApp (funj.uj_val, Array.map j_val seen)) typ)
          rest
    in
    match Evarconv.unify_leq_delay env sigma hj.uj_type c1 with
    | sigma ->
      apply_rec sigma (n+1) subs c2 restjl
    | exception Evarconv.UnableToUnify (sigma,error) ->
      error_cant_apply_bad_type env sigma ~error (n, c1, hj.uj_type) funj argjv
  in
  apply_rec sigma 1 (Esubst.subs_id 0) funj.uj_type (Array.to_list argjv)

let judge_of_applied ~check env sigma funj argjv =
  let sigma =
    if check then
      let (sigma, _) = judge_of_apply_core env sigma funj argjv in
      sigma
    else sigma
  in
  let typ = hnf_prod_appvect env sigma (j_type funj) (Array.map j_val argjv) in
  sigma, { uj_val = (mkApp (j_val funj, Array.map j_val argjv)); uj_type = typ }

(* XXX check_hyps_inclusion should now be cheap enough to always do *)
let judge_of_applied_inductive_knowing_parameters ~check env sigma (ind, u) argjv =
  let (mib,_ as specif) = Inductive.lookup_mind_specif env ind in
  let () = if check then EConstr.check_hyps_inclusion env (GR.IndRef ind) mib.mind_hyps in
  let sigma, paramstyp = fresh_template_context env sigma ind specif argjv in
  let u0 = EInstance.kind sigma u in
  let ty, csts = Inductive.type_of_inductive_knowing_parameters (specif, u0) paramstyp in
  let sigma = Evd.add_poly_constraints ~src:UState.Internal sigma csts in
  let funj = { uj_val = mkIndU (ind, u); uj_type = EConstr.of_constr (rename_type env ty (GR.IndRef ind)) } in
  judge_of_applied ~check env sigma funj argjv

let judge_of_applied_constructor_knowing_parameters ~check env sigma ((ind, _ as cstr), u) argjv =
  let (mib,_ as specif) = Inductive.lookup_mind_specif env ind in
  let () = if check then EConstr.check_hyps_inclusion env (GR.IndRef ind) mib.mind_hyps in
  let sigma, paramstyp = fresh_template_context env sigma ind specif argjv in
  let u0 = EInstance.kind sigma u in
  let ty, csts = Inductive.type_of_constructor_knowing_parameters (cstr, u0) specif paramstyp in
  let sigma = Evd.add_poly_constraints ~src:UState.Internal sigma csts in
  let funj = { uj_val = mkConstructU (cstr, u); uj_type = (EConstr.of_constr (rename_type env ty (GR.ConstructRef cstr))) } in
  judge_of_applied ~check env sigma funj argjv

let judge_of_apply env sigma fj args =
  match EConstr.kind sigma fj.uj_val with
  | Ind (ind, u) when EInstance.is_empty u && Environ.template_polymorphic_ind ind env ->
    judge_of_applied_inductive_knowing_parameters ~check:true env sigma (ind, u) args
  | Construct (cstr, u) when EInstance.is_empty u && Environ.template_polymorphic_ind (fst cstr) env ->
    judge_of_applied_constructor_knowing_parameters ~check:true env sigma (cstr, u) args
  | _ ->
    (* No template polymorphism *)
    judge_of_apply_core env sigma fj args

let checked_appvect env sigma f args =
  let mk c = Retyping.get_judgment_of env sigma c in
  let sigma, j = judge_of_apply env sigma (mk f) (Array.map mk args) in
  sigma, j.uj_val

let checked_applist env sigma f args = checked_appvect env sigma f (Array.of_list args)

let check_branch_types env sigma (ind,u) cj (lfj,explft) =
  if not (Int.equal (Array.length lfj) (Array.length explft)) then
    error_number_branches env sigma cj (Array.length explft);
  Array.fold_left2_i (fun i sigma lfj explft ->
      match Evarconv.unify_leq_delay env sigma lfj.uj_type explft with
      | sigma -> sigma
      | exception Evarconv.UnableToUnify _ ->
        error_ill_formed_branch env sigma cj.uj_val ((ind,i+1),u) lfj.uj_type explft)
    sigma lfj explft

let is_correct_arity env sigma c pj ind specif params =
  let arsign = make_arity_signature env sigma true (make_ind_family (ind,params)) in
  let error rtnsort = Pretype_errors.error_elim_arity env sigma ind c rtnsort in
  let rec srec env sigma pt ar =
    let pt' = whd_all env sigma pt in
    match EConstr.kind sigma pt', ar with
    | Prod (na1,a1,t), (LocalAssum (_,a1'))::ar' ->
      begin match Evarconv.unify_leq_delay env sigma a1 a1' with
        | exception Evarconv.UnableToUnify _ -> error None
        | sigma ->
          srec (push_rel (LocalAssum (na1,a1)) env) sigma t ar'
      end
    | Sort s, [] ->
      begin match is_squashed sigma (specif, snd ind) with
      | None -> sigma, s
      | Some squash ->
        let sigma =
          try squash_elim_sort sigma squash s
          with UGraph.UniverseInconsistency _ -> error (Some s)
        in
        sigma, s
      end
    | Evar (ev,_), [] ->
       let sigma, s = Evd.fresh_sort_in_quality sigma (elim_sort specif) in
       let sigma = Evd.define ev (mkSort s) sigma in
       sigma, s
    | _, (LocalDef _ as d)::ar' ->
        srec (push_rel d env) sigma (lift 1 pt') ar'
    | _ ->
        error None
  in
  srec env sigma pj.uj_type (List.rev arsign)

let lambda_applist_decls sigma n c l =
  let rec app n subst t l =
    if Int.equal n 0 then
      if l == [] then substl subst t
      else anomaly (Pp.str "Not enough arguments.")
    else match EConstr.kind sigma t, l with
    | Lambda(_,_,c), arg::l -> app (n-1) (arg::subst) c l
    | LetIn(_,b,_,c), _ -> app (n-1) (substl subst b::subst) c l
    | _ -> anomaly (Pp.str "Not enough lambda/let's.") in
  app n [] c l

let type_case_branches env sigma (ind,largs) specif pj c =
  let nparams = inductive_params specif in
  let (params,realargs) = List.chop nparams largs in
  let p = pj.uj_val in
  let sigma, ps = is_correct_arity env sigma c pj ind specif params in
  let ind = on_snd EConstr.Unsafe.to_instance ind in
  let params = List.map EConstr.Unsafe.to_constr params in
  let lc = build_branches_type ind specif params (EConstr.to_constr ~abort_on_undefined_evars:false sigma p) in
  let lc = Array.map EConstr.of_constr lc in
  let n = (snd specif).Declarations.mind_nrealdecls in
  let ty = whd_betaiota env sigma (lambda_applist_decls sigma (n+1) p (realargs@[c])) in
  sigma, (lc, ty, ESorts.relevance_of_sort ps)

let unify_relevance sigma r1 r2 =
  match ERelevance.kind sigma r1, ERelevance.kind sigma r2 with
  | Relevant, Relevant | Irrelevant, Irrelevant -> Some sigma
  | Relevant, Irrelevant | Irrelevant, Relevant -> None
  | Irrelevant, RelevanceVar q | RelevanceVar q, Irrelevant ->
    let sigma =
      Evd.add_constraints sigma
        (UnivProblem.Set.singleton (UnivProblem.QEq (Sorts.Quality.qsprop, QVar q)))
    in
    Some sigma
  | Relevant, RelevanceVar q | RelevanceVar q, Relevant ->
    let sigma =
      Evd.add_constraints sigma
        (UnivProblem.Set.singleton (UnivProblem.QLeq (Sorts.Quality.qprop, QVar q)))
    in
    Some sigma
  | RelevanceVar q1, RelevanceVar q2 ->
    if Sorts.QVar.equal q1 q2 then Some sigma
    else
      let sigma =
        Evd.add_constraints sigma
          (UnivProblem.Set.singleton (UnivProblem.QEq (Sorts.Quality.QVar q1, Sorts.Quality.QVar q2)))
      in
      Some sigma

let judge_of_case env sigma case ci (pj,rp) iv cj lfj =
  let ((ind, u), spec) =
    try find_mrectype env sigma cj.uj_type
    with Not_found -> error_case_not_inductive env sigma cj in
  let specif = lookup_mind_specif env ind in
  let () = if Inductive.is_private specif then Type_errors.error_case_on_private_ind env ind in
  let indspec = ((ind, u), spec) in
  let sigma, (bty,rslty,rci) = type_case_branches env sigma indspec specif pj cj.uj_val in
  (* should we have evar map aware should_invert_case? *)
  let sigma, rp =
    match unify_relevance sigma rp rci with
    | None ->
      raise_type_error (env,sigma,Type_errors.BadCaseRelevance (rp, mkCase case))
    | Some sigma -> sigma, rci
  in
  let ind = on_snd (EInstance.kind sigma) (fst indspec) in
  let () = check_case_info env ind ci in
  let sigma = check_branch_types env sigma ind cj (lfj,bty) in
  let () = if (match iv with | NoInvert -> false | CaseInvert _ -> true)
              != Inductiveops.Internal.should_invert_case env sigma (ERelevance.kind sigma rp) ci
    then Type_errors.error_bad_invert env
  in
  sigma, { uj_val  = mkCase case;
           uj_type = rslty }

let check_type_fixpoint ?loc env sigma lna lar vdefj =
  let lt = Array.length vdefj in
  assert (Int.equal (Array.length lar) lt);
  Array.fold_left2_i (fun i sigma defj ar ->
      match Evarconv.unify_leq_delay env sigma defj.uj_type (lift lt ar) with
      | sigma -> sigma
      | exception Evarconv.UnableToUnify _ ->
        error_ill_typed_rec_body ?loc env sigma
          i lna vdefj (Array.map (fun ty -> lift lt ty) lar))
    sigma vdefj lar


(* FIXME: might depend on the level of actual parameters!*)
let check_allowed_sort env sigma ind c p =
  let specif = lookup_mind_specif env (fst ind) in
  let pj = Retyping.get_judgment_of env sigma p in
  let _, s = whd_decompose_prod env sigma pj.uj_type in
  let sort =  match EConstr.kind sigma s with
    | Sort s -> s
    | _ -> error_elim_arity env sigma ind c None
  in
  match Inductiveops.make_allowed_elimination sigma (specif, (snd ind)) sort with
  | Some sigma -> sigma, ESorts.relevance_of_sort sort
  | None -> error_elim_arity env sigma ind c (Some sort)

let check_actual_type env sigma cj t =
  try Evarconv.unify_leq_delay env sigma cj.uj_type t
  with Evarconv.UnableToUnify (sigma,e) -> error_actual_type env sigma cj t e

let judge_of_cast env sigma cj k tj =
  let expected_type = tj.utj_val in
  let sigma = check_actual_type env sigma cj expected_type in
  sigma, { uj_val = mkCast (cj.uj_val, k, expected_type);
           uj_type = expected_type }

let check_fix_with_elims env sigma fix =
  let evars = Evd.evar_handler sigma in
  let sorts_opt = check_fix_pre_sorts ~evars env fix in
  Option.fold_left (List.fold_left (fun sigma (ind_sort, out_sort) ->
      let elim_to = Inductive.eliminates_to @@ Evd.elim_graph sigma in
      if not (is_allowed_fixpoint elim_to ind_sort out_sort) then
        Evd.set_elim_to sigma (Sorts.quality ind_sort) (Sorts.quality out_sort)
      else
        sigma
    )) sigma sorts_opt

let check_fix env sigma pfix =
  let inj c = EConstr.to_constr ~abort_on_undefined_evars:false sigma c in
  let (idx, (ids, cs, ts)) = pfix in
  let ids = Array.map EConstr.Unsafe.to_binder_annot ids in
  let fix = (idx, (ids, Array.map inj cs, Array.map inj ts)) in
  check_fix_with_elims env sigma fix

let check_cofix env sigma pcofix =
  let inj c = EConstr.to_constr sigma c in
  let (idx, (ids, cs, ts)) = pcofix in
  let ids = Array.map EConstr.Unsafe.to_binder_annot ids in
  check_cofix ~evars:(Evd.evar_handler sigma) env (idx, (ids, Array.map inj cs, Array.map inj ts))

(* The typing machine with universes and existential variables. *)

let judge_of_sprop =
  { uj_val = EConstr.mkSProp;
    uj_type = EConstr.type1 }

let judge_of_prop =
  { uj_val = EConstr.mkProp;
    uj_type = EConstr.mkSort (ESorts.type1) }

let judge_of_set =
  { uj_val = EConstr.mkSet;
    uj_type = EConstr.mkSort (ESorts.type1) }

let judge_of_sort s =
  let u = Typeops.type_of_sort s in
  { uj_val = EConstr.mkSort (ESorts.make s); uj_type = EConstr.of_constr u }

let type_of_relative env n =
  EConstr.of_constr (Typeops.type_of_relative env n)

let judge_of_relative env v =
  { uj_val = mkRel v; uj_type = type_of_relative env v }

let type_of_variable env id =
  EConstr.of_constr (Typeops.type_of_variable env id)

let judge_of_variable env id =
  { uj_val = mkVar id; uj_type = type_of_variable env id }

let judge_of_projection env sigma p cj =
  let pr, pty = lookup_projection p env in
  let sigma, (ind,u), args =
    let (t, l) = EConstr.decompose_app sigma (whd_all env sigma cj.uj_type) in
    match EConstr.kind sigma t with
    | Ind ind -> sigma, ind, l
    | Evar ev when Array.is_empty l ->
      (* The type of the record is not known yet: as for the type of an
         applied function, it is refined to the only possible one, the
         record type of the projection applied to unknown parameters. *)
      Evardefine.define_evar_as_inductive env sigma ev (Names.Projection.inductive p)
    | _ -> error_case_not_inductive env sigma cj
  in
  let pr = Vars.subst_instance_relevance u (ERelevance.make pr) in
  let ty = Vars.subst_instance_constr u (EConstr.of_constr pty) in
  let ty = substl (cj.uj_val :: Array.rev_to_list args) ty in
  sigma,
  {uj_val = EConstr.mkProj (p,pr,cj.uj_val);
   uj_type = ty}

let judge_of_abstraction env sigma name var j =
  let r = ESorts.relevance_of_sort var.utj_type in
  { uj_val = mkLambda (make_annot name r, var.utj_val, j.uj_val);
    uj_type = mkProd (make_annot name r, var.utj_val, j.uj_type) }

let judge_of_product env sigma name t1 t2 =
  let s1 = ESorts.kind sigma t1.utj_type in
  let s2 = ESorts.kind sigma t2.utj_type in
  let r = ERelevance.make @@ Sorts.relevance_of_sort s1 in
  let s = ESorts.make (Typeops.sort_of_product env s1 s2) in
  { uj_val = mkProd (make_annot name r, t1.utj_val, t2.utj_val);
    uj_type = mkSort s }

let judge_of_letin env sigma name defj typj j =
  let r = ESorts.relevance_of_sort typj.utj_type in
  { uj_val = mkLetIn (make_annot name r, defj.uj_val, typj.utj_val, j.uj_val) ;
    uj_type = subst1 defj.uj_val j.uj_type }

let type_of_constant env sigma (c,u) =
  let open Declarations in
  let cb = EConstr.lookup_constant env sigma c in
  let () = EConstr.check_hyps_inclusion env (GR.ConstRef c) cb.const_hyps in
  let u = EInstance.kind sigma u in
  let uctx = Declareops.constant_polymorphic_context cb in
  let csts = UVars.AbstractContext.instantiate u uctx in
  let ty = CVars.subst_instance_constr u cb.const_type in
  let sigma = Evd.add_poly_constraints ~src:UState.Internal sigma csts in
  sigma, (EConstr.of_constr (rename_type env ty (GR.ConstRef c)))

let type_of_inductive env sigma (ind,u) =
  let open Declarations in
  let (mib,_ as specif) = Inductive.lookup_mind_specif env ind in
  let () = EConstr.check_hyps_inclusion env (GR.IndRef ind) mib.mind_hyps in
  let u = EInstance.kind sigma u in
  let ty, csts = Inductive.constrained_type_of_inductive (specif,u) in
  let sigma = Evd.add_poly_constraints ~src:UState.Internal sigma csts in
  sigma, (EConstr.of_constr (rename_type env ty (GR.IndRef ind)))

let type_of_constructor env sigma ((ind,_ as ctor),u) =
  let open Declarations in
  let (mib,_ as specif) = Inductive.lookup_mind_specif env ind in
  let () = EConstr.check_hyps_inclusion env (GR.IndRef ind) mib.mind_hyps in
  let u = EInstance.kind sigma u in
  let ty, csts = Inductive.constrained_type_of_constructor (ctor,u) specif in
  let sigma = Evd.add_poly_constraints ~src:UState.Internal sigma csts in
  sigma, (EConstr.of_constr (rename_type env ty (GR.ConstructRef ctor)))

let type_of_int env = EConstr.of_constr (Typeops.type_of_int env)

let judge_of_int env v =
  { uj_val = mkInt v; uj_type = type_of_int env }

let type_of_float env = EConstr.of_constr (Typeops.type_of_float env)

let judge_of_float env v =
  { uj_val = mkFloat v; uj_type = type_of_float env }

let type_of_string env = EConstr.of_constr (Typeops.type_of_string env)

let judge_of_string env v =
  { uj_val = mkString v; uj_type = type_of_string env }

let judge_of_array env sigma u tj defj tyj =
  let () = if Uint63.(lt Parray.max_length (of_int (Array.length tj))) then
      raise_type_error (env, sigma, TooLargeArrayLiteral (Array.length tj))
  in
  let ulev = match UVars.Instance.to_array u with
    | [||], [|u|] -> u
    | _ -> assert false
  in
  let sigma = Evd.set_leq_sort sigma tyj.utj_type
      (ESorts.make (Sorts.sort_of_univ (Univ.Universe.make ulev)))
  in
  let check_one sigma j = check_actual_type env sigma j tyj.utj_val in
  let sigma = check_one sigma defj in
  let sigma = Array.fold_left check_one sigma tj in
  let arr = EConstr.of_constr @@ Typeops.type_of_array env u in
  let j = make_judge (mkArray(EInstance.make u, Array.map j_val tj, defj.uj_val, tyj.utj_val))
      (mkApp (arr, [|tyj.utj_val|]))
  in
  sigma, j

type ('constr,'types,'r) bad_relevance =
| BadRelevanceBinder of 'r * ('constr,'types,'r) Context.Rel.Declaration.pt
| BadRelevanceCase of 'r * 'constr

let bad_relevance_warning =
  CWarnings.create_warning ~name:"bad-relevance" ~default:CWarnings.AsError ()

let bad_relevance_msg = CWarnings.create_msg bad_relevance_warning ()
(* no need for default printer, pretyping is always linked with himsg in practice *)

let warn_bad_relevance_binder ?loc env sigma rlv bnd =
  match CWarnings.warning_status bad_relevance_warning with
| CWarnings.Disabled | CWarnings.Enabled ->
  CWarnings.warn bad_relevance_msg ?loc (env,sigma,BadRelevanceBinder (rlv, bnd))
| CWarnings.AsError ->
  Loc.raise ?loc (PretypeError (env, sigma, TypingError (Type_errors.BadBinderRelevance (rlv, bnd))))

type relevance_preunify =
  | Trivial
  | Impossible
  | DummySort of ESorts.t

let check_binder_relevance env sigma s decl =
  let preunify = match ESorts.kind sigma s, ERelevance.kind sigma (get_relevance decl) with
    | (Prop | Set | Type _ | GSort _), Relevant -> Trivial
    | (Prop | Set | Type _ | GSort _), Irrelevant -> Impossible
    | SProp, Irrelevant -> Trivial
    | SProp, Relevant -> Impossible
    | VSort (_,l), RelevanceVar q' -> DummySort (ESorts.make (Sorts.vsort q' l))
    | (SProp | Prop | Set), RelevanceVar q ->
      DummySort (ESorts.make (Sorts.vsort q Univ.Universe.type0))
    | (Type l | GSort (_, l)), RelevanceVar q -> DummySort (ESorts.make (Sorts.vsort q l))
    | VSort (_,l), Relevant ->
       begin
         match ERelevance.kind sigma (ESorts.relevance_of_sort s) with
         | Irrelevant -> Impossible
         | Relevant -> Trivial
         | RelevanceVar _ -> DummySort (ESorts.make (Sorts.sort_of_univ l))
       end
    | VSort _, Irrelevant -> DummySort ESorts.sprop
  in
  let unify = match preunify with
    | Trivial -> Some sigma
    | Impossible -> None
    | DummySort s' ->
      match Evd.set_leq_sort sigma s s' with
      | sigma -> Some sigma
      | exception UGraph.UniverseInconsistency _ -> None
  in
  match unify with
  | Some sigma -> sigma, decl
  | None ->
    (* TODO always anomaly *)
    let rs = ESorts.relevance_of_sort s in
    let () =
      if Environ.ignore_elim_constraints env then () else
      warn_bad_relevance_binder env sigma rs decl
    in
    sigma, set_annot { (get_annot decl) with binder_relevance = rs } decl

(* Differences with the kernel-side HConstr: we allow evars and don't try to
   outsmart sharing with different environments. *)
module HTConstr :
sig
  type t
  type table
  val empty_table : unit -> table
  val make : table -> Constr.t -> t
  val make_app : table -> t -> t array -> t
  val make_binder : table -> rel_declaration -> t -> t
  val proj : t -> EConstr.t
  val kind : t -> (t, t, Sorts.t, UVars.Instance.t, Sorts.relevance) Constr.kind_of_term
  val find_judgment : env -> t -> unsafe_judgment option
  val add_judgment : env -> t -> unsafe_judgment -> unit
end =
struct

type t = {
  proj : Constr.t;
  self : (t, t, Sorts.t, UVars.Instance.t, Sorts.relevance) Constr.kind_of_term;
  max_rel : int;
  hash : int;
  mutable memo : (Constr.rel_context * unsafe_judgment) option;
}

type kind = (t, t, Sorts.t, UVars.Instance.t, Sorts.relevance) Constr.kind_of_term

let eq_annot na1 na2 = Context.eq_annot Names.Name.equal Sorts.relevance_equal na1 na2

let eq_ci ci1 ci2 =
  Names.Ind.UserOrd.equal ci1.ci_ind ci2.ci_ind &&
  Int.equal ci1.ci_npar ci2.ci_npar &&
  Array.equal Int.equal ci1.ci_cstr_ndecls ci2.ci_cstr_ndecls &&
  Array.equal Int.equal ci1.ci_cstr_nargs ci2.ci_cstr_nargs &&
  ci1.ci_pp_info.style == ci2.ci_pp_info.style

let eq_kind (k1 : kind) (k2 : kind) = match k1, k2 with
| Rel n1, Rel n2 -> Int.equal n1 n2
| Meta m1, Meta m2 -> Int.equal m1 m2
| Var id1, Var id2 -> Names.Id.equal id1 id2
| Int i1, Int i2 -> Uint63.equal i1 i2
| Float f1, Float f2 -> Float64.equal f1 f2
| String s1, String s2 -> Pstring.equal s1 s2
| Sort s1, Sort s2 -> Sorts.equal s1 s2
| Cast (c1, k1, t1), Cast (c2, k2, t2) ->
  c1 == c2 && Glob_ops.cast_kind_eq k1 k2 && t1 == t2
| Prod (na1, t1, c1), Prod (na2, t2, c2) ->
  eq_annot na1 na2 && t1 == t2 && c1 == c2
| Lambda (na1, t1, c1), Lambda (na2, t2, c2) ->
  eq_annot na1 na2 && t1 == t2 && c1 == c2
| LetIn (na1, b1, t1, c1), LetIn (na2, b2, t2, c2) ->
  eq_annot na1 na2 && b1 == b2 && t1 == t2 && c1 == c2
| App (f1, al1), App (f2, al2) ->
  f1 == f2 && Array.equal (==) al1 al2
| Proj (p1, r1, c1), Proj (p2, r2, c2) ->
  Names.Projection.UserOrd.equal p1 p2 && Sorts.relevance_equal r1 r2 && c1 == c2
| Evar (e1, l1), Evar (e2, l2) ->
  Evar.equal e1 e2 && SList.equal (==) l1 l2
| Const (c1, u1), Const (c2, u2) ->
  Names.Constant.UserOrd.equal c1 c2 && UVars.Instance.equal u1 u2
| Ind (c1, u1), Ind (c2, u2) ->
  Names.Ind.UserOrd.equal c1 c2 && UVars.Instance.equal u1 u2
| Construct (c1, u1), Construct (c2, u2) ->
  Names.Construct.UserOrd.equal c1 c2 && UVars.Instance.equal u1 u2
| Case (ci1, u1, pms1, ((nas1, p1), r1), iv1, c1, bl1),
  Case (ci2, u2, pms2, ((nas2, p2), r2), iv2, c2, bl2) ->
  eq_ci ci1 ci2 && UVars.Instance.equal u1 u2 && Array.equal (==) pms1 pms2 &&
  Array.equal eq_annot nas1 nas2 && p1 == p2 && Sorts.relevance_equal r1 r2 &&
  begin match iv1, iv2 with
  | NoInvert, NoInvert -> true
  | CaseInvert { indices = i1 }, CaseInvert { indices = i2 } -> Array.equal (==) i1 i2
  | (NoInvert | CaseInvert _), _ -> false
  end &&
  c1 == c2 &&
  Array.equal (fun (nas1, b1) (nas2, b2) -> Array.equal eq_annot nas1 nas2 && b1 == b2) bl1 bl2
| Fix ((ln1, i1), (na1, tl1, bl1)), Fix ((ln2, i2), (na2, tl2, bl2)) ->
  Int.equal i1 i2 && Array.equal Int.equal ln1 ln2 && Array.equal eq_annot na1 na2 &&
  Array.equal (==) tl1 tl2 && Array.equal (==) bl1 bl2
| CoFix (i1, (na1, tl1, bl1)), CoFix (i2, (na2, tl2, bl2)) ->
  Int.equal i1 i2 && Array.equal eq_annot na1 na2 &&
  Array.equal (==) tl1 tl2 && Array.equal (==) bl1 bl2
| Array (u1, t1, def1, ty1), Array (u2, t2, def2, ty2) ->
  UVars.Instance.equal u1 u2 && Array.equal (==) t1 t2 && def1 == def2 && ty1 == ty2
| (Rel _ | Meta _ | Var _ | Sort _ | Prod _ | Lambda _ | LetIn _ | App _ | Cast _
  | Proj _ | Evar _ | Const _ | Ind _ | Construct _ | Case _ | Fix _
  | CoFix _ | Int _ | Float _ | String _ | Array _), _ -> false

let fold_kind f accu (k : kind) = match k with
| Rel _ | Meta _ | Var _ | Sort _ | Const _ | Ind _ | Construct _
| Int _ | Float _ | String _ -> accu
| Cast (c, _, t) -> f (f accu c) t
| Prod (_, t, c) | Lambda (_, t, c) -> f (f accu t) c
| LetIn (_, b, t, c) -> f (f (f accu b) t) c
| App (h, al) -> Array.fold_left f (f accu h) al
| Proj (_, _, c) -> f accu c
| Evar (_, al) -> SList.Skip.fold f accu al
| Case (_, _, pms, ((_, p), _), iv, c, bl) ->
  let accu = Array.fold_left f accu pms in
  let accu = f accu p in
  let accu = match iv with NoInvert -> accu | CaseInvert { indices } -> Array.fold_left f accu indices in
  let accu = f accu c in
  Array.fold_left (fun accu (_, b) -> f accu b) accu bl
| Fix (_, (_, tl, bl)) | CoFix (_, (_, tl, bl)) ->
  Array.fold_left f (Array.fold_left f accu tl) bl
| Array (_, t, def, ty) -> f (f (Array.fold_left f accu t) def) ty

module Self =
struct
  type nonrec t = t
  let hash c = c.hash
  let equal c1 c2 = eq_kind c1.self c2.self
end

module Table = Hashtbl.Make(Self)

type table = t Table.t

let empty_table () = Table.create 17

let hash_kind proj (k : kind) =
  let base = match k with
  | Rel _ | Meta _ | Var _ | Sort _ | Const _ | Ind _ | Construct _
  | Int _ | Float _ | String _ -> Termops.ConstrData.hash proj
  | Evar (e, _) -> Hashset.Combine.combine 3 (Evar.hash e)
  | Cast _ -> 5 | Prod _ -> 6 | Lambda _ -> 7 | LetIn _ -> 8 | App _ -> 9
  | Case _ -> 13 | Fix _ -> 14 | CoFix _ -> 15 | Proj _ -> 16 | Array _ -> 20
  in
  fold_kind (fun accu c -> Hashset.Combine.combine accu c.hash) base k

let max (i : int) (j : int) = if i < j then j else i
let liftn k (i : int) = if i <= k then 0 else i - k
let max_data accu c = max accu c.max_rel
let max_array v = Array.fold_left max_data 0 v

let data_kind (k : kind) = match k with
| Rel n -> n
| Prod (_, t, c) | Lambda (_, t, c) -> max t.max_rel (liftn 1 c.max_rel)
| LetIn (_, b, t, c) -> max b.max_rel (max t.max_rel (liftn 1 c.max_rel))
| Case (_, _, pms, ((nas, p), _), iv, c, bl) ->
  let ivd = match iv with NoInvert -> 0 | CaseInvert { indices } -> max_array indices in
  let bld = Array.fold_left (fun accu (nas, b) -> max accu (liftn (Array.length nas) b.max_rel)) 0 bl in
  max (max_array pms) (max (liftn (Array.length nas) p.max_rel) (max ivd (max c.max_rel bld)))
| Fix (_, (nas, tl, bl)) | CoFix (_, (nas, tl, bl)) ->
  max (max_array tl) (liftn (Array.length nas) (max_array bl))
| Meta _ | Var _ | Sort _ | Const _ | Ind _ | Construct _ | Int _ | Float _ | String _
| Evar _ | Cast _ | App _ | Proj _ | Array _ ->
  fold_kind max_data 0 k

let node table proj self =
  let ans = { proj; self; max_rel = data_kind self; hash = hash_kind proj self; memo = None } in
  match Table.find_opt table ans with
  | Some ans -> ans
  | None ->
    let () = Table.add table ans ans in
    ans

let rec make table c =
  let mk c = make table c in
  let self : kind = match Constr.kind c with
  | Rel n -> Rel n
  | Meta m -> Meta m
  | Var id -> Var id
  | Sort s -> Sort s
  | Const c -> Const c
  | Ind ind -> Ind ind
  | Construct cstr -> Construct cstr
  | Int i -> Int i
  | Float f -> Float f
  | String s -> String s
  | Cast (c, k, t) -> Cast (mk c, k, mk t)
  | Prod (na, t, c) -> Prod (na, mk t, mk c)
  | Lambda (na, t, c) -> Lambda (na, mk t, mk c)
  | LetIn (na, b, t, c) -> LetIn (na, mk b, mk t, mk c)
  | App (f, al) -> App (mk f, Array.map mk al)
  | Proj (p, r, c) -> Proj (p, r, mk c)
  | Evar (e, al) -> Evar (e, SList.Skip.map mk al)
  | Case (ci, u, pms, ((nas, p), r), iv, c, bl) ->
    let iv = match iv with
    | NoInvert -> NoInvert
    | CaseInvert { indices } -> CaseInvert { indices = Array.map mk indices }
    in
    Case (ci, u, Array.map mk pms, ((nas, mk p), r), iv, mk c, Array.map (fun (nas, b) -> (nas, mk b)) bl)
  | Fix (fi, (nas, tl, bl)) -> Fix (fi, (nas, Array.map mk tl, Array.map mk bl))
  | CoFix (i, (nas, tl, bl)) -> CoFix (i, (nas, Array.map mk tl, Array.map mk bl))
  | Array (u, t, def, ty) -> Array (u, Array.map mk t, mk def, mk ty)
  in
  node table c self

let make_app table f args =
  if Array.is_empty args then f
  else
    let proj = Constr.mkApp (f.proj, Array.map (fun c -> c.proj) args) in
    let self = match f.self with
    | App (h, al) -> App (h, Array.append al args)
    | _ -> App (f, args)
    in
    node table proj self

let make_binder table decl body =
  let to_annot na = Context.map_annot_relevance_het EConstr.Unsafe.to_relevance na in
  match decl with
  | LocalAssum (na, t) ->
    let na = to_annot na in
    let t = EConstr.Unsafe.to_constr t in
    node table (Constr.mkLambda (na, t, body.proj)) (Lambda (na, make table t, body))
  | LocalDef (na, b, t) ->
    let na = to_annot na in
    let b = EConstr.Unsafe.to_constr b in
    let t = EConstr.Unsafe.to_constr t in
    node table (Constr.mkLetIn (na, b, t, body.proj)) (LetIn (na, make table b, make table t, body))

let proj c = EConstr.of_constr c.proj
let kind c = c.self

let find_judgment env c = match c.memo with
| None -> None
| Some (ctx, j) ->
  if Int.equal c.max_rel 0 || ctx == Environ.rel_context env then Some j else None

let add_judgment env c j =
  c.memo <- Some (Environ.rel_context env, j)

end

type execute_state = {
  table : HTConstr.table;
  check_evars : bool;
}

let rec execute_node tbl env sigma n =
  match HTConstr.find_judgment env n with
  | Some j -> sigma, j
  | None ->
    let sigma, j = execute_node_core tbl env sigma n in
    let () = HTConstr.add_judgment env n j in
    sigma, j

and execute_node_core tbl env sigma n =
  let cstr = HTConstr.proj n in
  match HTConstr.kind n with
    | Meta n -> assert false (* Typing should always be performed on meta-free terms *)

    | Evar _ ->
        let cstr = whd_evar sigma cstr in
        begin match EConstr.kind sigma cstr with
        | Evar ev when not tbl.check_evars ->
          sigma, { uj_val = cstr; uj_type = EConstr.existential_type sigma ev }
        | Evar ev ->
          let ty = EConstr.existential_type sigma ev in
          let sigma, jty = execute_node tbl env sigma (HTConstr.make tbl.table (EConstr.Unsafe.to_constr ty)) in
          let sigma, jty = assumption_of_judgment env sigma jty in
          sigma, { uj_val = cstr; uj_type = jty }
        | _ -> execute_node tbl env sigma (HTConstr.make tbl.table (EConstr.Unsafe.to_constr cstr))
        end

    | Rel n ->
        sigma, judge_of_relative env n

    | Var id ->
        sigma, judge_of_variable env id

    | Const (c, u) ->
        let sigma, ty = type_of_constant env sigma (c, EInstance.make u) in
        sigma, make_judge cstr ty

    | Ind (ind, u) ->
        let sigma, ty = type_of_inductive env sigma (ind, EInstance.make u) in
        sigma, make_judge cstr ty

    | Construct (ctor, u) ->
        let sigma, ty = type_of_constructor env sigma (ctor, EInstance.make u) in
        sigma, make_judge cstr ty

    | Case (ci, u, pms, ((nas, p), r), iv, c, lf) ->
        let proj = HTConstr.proj in
        let case_iv = match iv with
          | NoInvert -> NoInvert
          | CaseInvert { indices } -> CaseInvert { indices = Array.map proj indices }
        in
        let case = (ci, EInstance.make u, Array.map proj pms,
                    ((Array.map EConstr.of_binder_annot nas, proj p), ERelevance.make r),
                    case_iv, proj c,
                    Array.map (fun (nas, b) -> (Array.map EConstr.of_binder_annot nas, proj b)) lf) in
        let (ci, _, _, ((pctx, _), rp), _, _, lfctx) = EConstr.annotate_case env sigma case in
        let wrap ctx body = List.fold_left (fun body decl -> HTConstr.make_binder tbl.table decl body) body ctx in
        let pn = wrap pctx p in
        let lfn = Array.map2 (fun (ctx, _) (_, b) -> wrap ctx b) lfctx lf in
        let sigma, cj = execute_node tbl env sigma c in
        let sigma, pj = execute_node tbl env sigma pn in
        let sigma, lfj = execute_nodes tbl env sigma lfn in
        let sigma = match iv with
          | NoInvert -> sigma
          | CaseInvert { indices } ->
            let ind = HTConstr.make tbl.table (Constr.mkIndU (ci.ci_ind, u)) in
            let t = HTConstr.make_app tbl.table ind (Array.append pms indices) in
            let sigma, tj = execute_node tbl env sigma t in
            let sigma, tj = type_judgment env sigma tj in
            let sigma = check_actual_type env sigma cj tj.utj_val in
            sigma
        in
        judge_of_case env sigma case ci (pj,rp) case_iv cj lfj

    | Fix ((vn,i as vni),recdef) ->
        let sigma, (_,tys,_ as recdef') = execute_recdef tbl env sigma recdef in
        let fix = (vni,recdef') in
        let sigma = check_fix env sigma fix in
        sigma, make_judge (mkFix fix) tys.(i)

    | CoFix (i,recdef) ->
        let sigma, (_,tys,_ as recdef') = execute_recdef tbl env sigma recdef in
        let cofix = (i,recdef') in
        check_cofix env sigma cofix;
        sigma, make_judge (mkCoFix cofix) tys.(i)

    | Sort s ->
      let s = ESorts.kind sigma (ESorts.make s) in
      if not (Environ.sprop_allowed env) && Sorts.is_sprop s then
        error_not_allowed_sprop env sigma
      else sigma, judge_of_sort s

    | Proj (p, _, c) ->
      let sigma, cj = execute_node tbl env sigma c in
      judge_of_projection env sigma p cj

    | App (f,args) ->
        let sigma, fj = execute_node tbl env sigma f in
        let sigma, jl = execute_nodes tbl env sigma args in
        judge_of_apply env sigma fj jl

    | Lambda (name,c1,c2) ->
        let name = EConstr.of_binder_annot name in
        let sigma, j = execute_node tbl env sigma c1 in
        let sigma, var = type_judgment env sigma j in
        let sigma, decl = check_binder_relevance env sigma var.utj_type (LocalAssum (name, var.utj_val)) in
        let env1 = push_rel decl env in
        let sigma, j' = execute_node tbl env1 sigma c2 in
        sigma, judge_of_abstraction env1 sigma name.binder_name var j'

    | Prod (name,c1,c2) ->
        let name = EConstr.of_binder_annot name in
        let sigma, j = execute_node tbl env sigma c1 in
        let sigma, varj = type_judgment env sigma j in
        let sigma, decl = check_binder_relevance env sigma varj.utj_type (LocalAssum (name, varj.utj_val)) in
        let env1 = push_rel decl env in
        let sigma, j' = execute_node tbl env1 sigma c2 in
        let sigma, varj' = type_judgment env1 sigma j' in
        sigma, judge_of_product env sigma name.binder_name varj varj'

     | LetIn (name,c1,c2,c3) ->
        let name = EConstr.of_binder_annot name in
        let sigma, j1 = execute_node tbl env sigma c1 in
        let sigma, j2 = execute_node tbl env sigma c2 in
        let sigma, j2 = type_judgment env sigma j2 in
        let sigma, _ =  judge_of_cast env sigma j1 DEFAULTcast j2 in
        let sigma, decl = check_binder_relevance env sigma j2.utj_type (LocalDef (name, j1.uj_val, j2.utj_val)) in
        let env1 = push_rel decl env in
        let sigma, j3 = execute_node tbl env1 sigma c3 in
        sigma, judge_of_letin env sigma name.binder_name j1 j2 j3

    | Cast (c,k,t) ->
        let sigma, cj = execute_node tbl env sigma c in
        let sigma, tj = execute_node tbl env sigma t in
        let sigma, tj = type_judgment env sigma tj in
        judge_of_cast env sigma cj k tj

    | Int i ->
        sigma, judge_of_int env i

    | Float f ->
        sigma, judge_of_float env f

    | String s ->
        sigma, judge_of_string env s

    | Array(u,t,def,ty) ->
      let sigma, tyj = execute_node tbl env sigma ty in
      let sigma, tyj = type_judgment env sigma tyj in
      let sigma, defj = execute_node tbl env sigma def in
      let sigma, tj = execute_nodes tbl env sigma t in
      judge_of_array env sigma (EInstance.kind sigma (EInstance.make u)) tj defj tyj

and execute_recdef tbl env sigma (names,lar,vdef) =
  let names = Array.map EConstr.of_binder_annot names in
  let sigma, larj = execute_nodes tbl env sigma lar in
  let sigma, lara = Array.fold_left_map (assumption_of_judgment env) sigma larj in
  let env1 = push_rec_types (names,lara,Array.map HTConstr.proj vdef) env in
  let sigma, vdefj = execute_nodes tbl env1 sigma vdef in
  let vdefv = Array.map j_val vdefj in
  let sigma = check_type_fixpoint env1 sigma names lara vdefj in
  sigma, (names,lara,vdefv)

and execute_nodes tbl env = Array.fold_left_map (execute_node tbl env)


let execute ?(check_evars=true) env sigma c =
  let tbl = { table = HTConstr.empty_table (); check_evars } in
  execute_node tbl env sigma (HTConstr.make tbl.table (EConstr.Unsafe.to_constr c))

let execute_array env sigma v =
  let tbl = { table = HTConstr.empty_table (); check_evars = true } in
  execute_nodes tbl env sigma (Array.map (fun c -> HTConstr.make tbl.table (EConstr.Unsafe.to_constr c)) v)

let check env sigma c t =
  let sigma, j = execute env sigma c in
  check_actual_type env sigma j t

(* Sort of a type *)

let sort_of env sigma c =
  let sigma, j = execute env sigma c in
  let sigma, a = type_judgment env sigma j in
  sigma, a.utj_type

(* Try to solve the existential variables by typing *)

let type_of ?(refresh=false) env sigma c =
  let sigma, j = execute env sigma c in
  (* side-effect on evdref *)
    if refresh then
      Evarsolve.refresh_universes ~onlyalg:true (Some false) env sigma j.uj_type
    else sigma, j.uj_type

let () = Hook.set Evarsolve.type_of_hook (fun env sigma c ->
  let sigma, j = execute ~check_evars:false env sigma c in
  sigma, j.uj_type)

let solve_evars env sigma c =
  let sigma, j = execute env sigma c in
  (* side-effect on evdref *)
  sigma, nf_evar sigma j.uj_val

let _ = Evarconv.set_solve_evars (fun env sigma c -> solve_evars env sigma c)

type change_kind = Same | Changed of {bodyonly : bool Lazy.t }

let merge_changes a b = match a,b with
  | Same, v | v, Same -> v
  | Changed {bodyonly=a}, Changed {bodyonly=b} ->
    Changed {bodyonly = lazy (Lazy.force a && Lazy.force b)}

let unchanged = function
  | Same -> true
  | Changed _ -> false

let bodyonly = function
  | Same -> true
  | Changed {bodyonly} -> Lazy.force bodyonly

let judge_of_apply_against env sigma changedf funj argjv =
  let rec apply_rec sigma changedf n subs typ = function
  | [] ->
    let typ = Vars.esubst Vars.lift_substituend subs typ in
    sigma,
    { uj_val  = mkApp (j_val funj, Array.map (fun (_,j) -> j_val j) argjv);
      uj_type = typ }
  | (changedh,hj)::restjl ->
    let sigma, c1, subs, c2 = match EConstr.kind sigma typ with
    | Prod (_, c1, c2) ->
      (* Fast path *)
      let c1 = Vars.esubst Vars.lift_substituend subs c1 in
      let subs = Esubst.subs_cons (Vars.make_substituend hj.uj_val) subs in
      sigma, c1, subs, c2
    | _ ->
      let typ = Vars.esubst Vars.lift_substituend subs typ in
      let subs = Esubst.subs_cons (Vars.make_substituend hj.uj_val) (Esubst.subs_id 0) in
      match EConstr.kind sigma (whd_all env sigma typ) with
      | Prod (_, c1, c2) -> sigma, c1, subs, c2
      | Evar ev ->
        let (sigma,t) = Evardefine.define_evar_as_product env sigma ev in
        let (_, c1, c2) = destProd sigma t in
        sigma, c1, subs, c2
      | _ ->
        error_cant_apply_not_functional env sigma funj (Array.map snd argjv)
    in
    if bodyonly changedf then begin match changedh with
      | Same -> apply_rec sigma changedf (n+1) subs c2 restjl
      | Changed {bodyonly=lazy true} ->
        (* TODO if non dependent product then changedf else bodyonly = false *)
        apply_rec sigma (Changed {bodyonly=lazy false}) (n+1) subs c2 restjl
      | Changed {bodyonly=lazy false} ->
        match Evarconv.unify_leq_delay env sigma hj.uj_type c1 with
        | sigma ->
          apply_rec sigma (Changed {bodyonly=lazy false}) (n+1) subs c2 restjl
        | exception Evarconv.UnableToUnify (sigma,error) ->
          error_cant_apply_bad_type env sigma ~error (n, c1, hj.uj_type) funj (Array.map snd argjv)
    end
    else
      match Evarconv.unify_leq_delay env sigma hj.uj_type c1 with
      | sigma ->
        apply_rec sigma changedf (n+1) subs c2 restjl
      | exception Evarconv.UnableToUnify (sigma,error) ->
        error_cant_apply_bad_type env sigma ~error (n, c1, hj.uj_type) funj (Array.map snd argjv)
  in
  apply_rec sigma changedf 1 (Esubst.subs_id 0) funj.uj_type (Array.to_list argjv)

(* Assuming "env |- good : some type", infer "env |- c : other type" *)
let rec recheck_against env sigma good c =
  if EConstr.eq_constr sigma good c then sigma, Same, make_judge c (Retyping.get_type_of env sigma c)
  else
    let assume_unchanged_type sigma =
      let gt = Retyping.get_type_of env sigma good in
      sigma, Changed {bodyonly=Lazy.from_val true}, make_judge c gt
    in
    let maybe_changed (sigma, j) =
      let bodyonly = lazy (EConstr.eq_constr sigma (Retyping.get_type_of env sigma good) j.uj_type) in
      let change = Changed {bodyonly} in
      sigma, change, j
    in
    let default () = maybe_changed (execute env sigma c) in
    match kind sigma good, kind sigma c with
    (* No subterms *)
    | _, (Meta _ | Rel _ | Var _ | Const _ | Ind _ | Construct _
         | Sort _ | Int _ | Float _ | String _) ->
      default ()

    (* Evar (todo deal with Evar differently??? execute recurses on its type)
       others: too annoying for now *)
    | _, (Evar _ | Fix _ | CoFix _ | LetIn _ | Array _) ->
     default ()

    | Case (gci, gu, gpms, gp, giv, gc, glf),
      Case (ci, u, pms, p, iv, c, lf) ->
      let (gci, (gp,_), giv, gc, glf) = EConstr.expand_case env sigma (gci, gu, gpms, gp, giv, gc, glf) in
      let case = (ci, u, pms, p, iv, c, lf) in
      let (ci, (p,rp), iv, c, lf) = EConstr.expand_case env sigma case in
      let sigma, changedc, cj = recheck_against env sigma gc c in
      let sigma, changedp, pj = recheck_against env sigma gp p in
      let (sigma, changedlf), lfj =
        if Array.length glf <> Array.length lf then
          Array.fold_left_map (fun (sigma,changed) c ->
              let sigma, j = execute env sigma c in
              (sigma, changed), j)
            (sigma, Changed {bodyonly=lazy false})
            lf
        else
          Array.fold_left2_map (fun (sigma,changed) good c ->
              let sigma, changed', t = recheck_against env sigma good c in
              (sigma, merge_changes changed changed'), t)
            (sigma,Same) glf lf
      in
      let sigma, changediv = match giv, iv with
        | _, NoInvert -> sigma, Same
        | NoInvert, CaseInvert {indices} ->
          (* likely bug but accept for now *)
          let args = Array.append pms indices in
          let t = mkApp (mkIndU (ci.ci_ind,u), args) in
          let sigma, tj = execute env sigma t in
          let sigma, tj = type_judgment env sigma tj in
          let sigma = check_actual_type env sigma cj tj.utj_val in
          sigma, Changed {bodyonly=Lazy.from_val false}
        | CaseInvert {indices=gindices}, CaseInvert {indices} ->
          let gargs = Array.append gpms gindices in
          let args = Array.append pms indices in
          let gt = mkApp (mkIndU (gci.ci_ind,u), gargs) in
          let t = mkApp (mkIndU (ci.ci_ind,u), args) in
          let sigma, changediv, tj = recheck_against env sigma gt t in
          let sigma, tj = type_judgment env sigma tj in
          let sigma = check_actual_type env sigma cj tj.utj_val in
          sigma, changediv
      in
      if unchanged changedc && unchanged changedp && unchanged changediv && bodyonly changedlf
      then assume_unchanged_type sigma
      else maybe_changed (judge_of_case env sigma case ci (pj,rp) iv cj lfj)

    | Proj (gp, _, gc),
      Proj (p, _, c) ->
      if not (QProjection.equal env gp p) then default ()
      else
        let sigma, changed, c = recheck_against env sigma gc c in
        maybe_changed (judge_of_projection env sigma p c)

    | App (gf, gargs),
      App (f, args) ->
      let glen = Array.length gargs in
      let len = Array.length args in
      if glen < len then
        (* We are rechecking f a1 ... an x1 ... xk against gf y1 ... yk with n > 0  *)
        let pre, args = Array.chop (len - glen) args in
        let sigma, fj = execute env sigma f in
        let sigma, prej = execute_array env sigma pre in
        let (sigma, changedargs), argsj =
          Array.fold_left2_map (fun (sigma, changed) good c ->
              let sigma, changed', t = recheck_against env sigma good c in
              (sigma, merge_changes changed changed'), t)
            (sigma, Same) gargs args
        in
        let jl = Array.append prej argsj in
        begin match EConstr.kind sigma f with
         | Ind (ind, u) when EInstance.is_empty u && Environ.template_polymorphic_ind ind env ->
           maybe_changed (judge_of_applied_inductive_knowing_parameters ~check:true env sigma (ind, u) jl)
         | Construct (cstr, u) when EInstance.is_empty u && Environ.template_polymorphic_ind (fst cstr) env ->
           maybe_changed (judge_of_applied_constructor_knowing_parameters ~check:true env sigma (cstr, u) jl)
         | _ ->
           (* No template polymorphism *)
           maybe_changed (judge_of_apply env sigma fj jl)
        end
      else
        (* We are rechecking f x1 ... xk against gf a1 ... an y1 ... yk with n >= 0 *)
        let pre, gargs = if len < glen then Array.chop (glen - len) gargs else [||], gargs in
        let (sigma, changedargs), jl =
          Array.fold_left2_map (fun (sigma,changed) good c ->
              let sigma, changed', t = recheck_against env sigma good c in
              (sigma, merge_changes changed changed'), (changed', t))
            (sigma,Same) gargs args
        in
        let sigma, changedf, fj =
          if Int.equal glen len then recheck_against env sigma gf f
          else
            let sigma, fj = execute env sigma f in
            let bodyonly = lazy begin
              let good = mkApp (gf, pre) in
              EConstr.eq_constr sigma (Retyping.get_type_of env sigma good) fj.uj_type
            end in
            let change = Changed {bodyonly} in
            sigma, change, fj
        in
        if unchanged changedargs && bodyonly changedf
        then assume_unchanged_type sigma
        else
          (* XXX could exploit change info when template *)
          begin match EConstr.kind sigma f with
           | Ind (ind, u) when EInstance.is_empty u && Environ.template_polymorphic_ind ind env ->
             let jl = Array.map snd jl in
             maybe_changed (judge_of_applied_inductive_knowing_parameters ~check:true env sigma (ind, u) jl)
           | Construct (cstr, u) when EInstance.is_empty u && Environ.template_polymorphic_ind (fst cstr) env ->
             let jl = Array.map snd jl in
             maybe_changed (judge_of_applied_constructor_knowing_parameters ~check:true env sigma (cstr, u) jl)
           | _ ->
             (* No template polymorphism *)
             maybe_changed (judge_of_apply_against env sigma changedf fj jl)
          end

    | Lambda (_, gc1, gc2),
      Lambda (name, c1, c2) ->
      let sigma, changedj, j = recheck_against env sigma gc1 c1 in
      let sigma, var = type_judgment env sigma j in
      let sigma, decl = check_binder_relevance env sigma var.utj_type (LocalAssum (name, var.utj_val)) in
      let env1 = push_rel decl env in
      let sigma, changedj', j' = if unchanged changedj then recheck_against env1 sigma gc2 c2
        else let sigma, j' = execute env1 sigma c2 in
          sigma, Changed {bodyonly=lazy false}, j'
      in
      sigma, merge_changes changedj' changedj, judge_of_abstraction env1 sigma name.binder_name var j'

    | Prod (_, gc1, gc2),
      Prod (name, c1, c2) ->
      let sigma, changedj, j = recheck_against env sigma gc1 c1 in
      let sigma, var = type_judgment env sigma j in
      let sigma, decl = check_binder_relevance env sigma var.utj_type (LocalAssum (name, var.utj_val)) in
      let env1 = push_rel decl env in
      let sigma, changedj', j' = if unchanged changedj then recheck_against env1 sigma gc2 c2
        else let sigma, j' = execute env1 sigma c2 in
          sigma, Changed {bodyonly=lazy false}, j'
      in
      let sigma, j' = type_judgment env1 sigma j' in
      sigma, merge_changes changedj' changedj, judge_of_product env1 sigma name.binder_name var j'

    | Cast (gc, _, gt),
      Cast (c, k, t) ->
      let sigma, changedc, cj = recheck_against env sigma gc c in
      let sigma, changedt, tj = recheck_against env sigma gt t in
      if unchanged changedt && bodyonly changedc
      then assume_unchanged_type sigma
      else
        let sigma, tj = type_judgment env sigma tj in
        maybe_changed (judge_of_cast env sigma cj k tj)

    | _, (Case _ | App _ | Lambda _ | Prod _ | Cast _ | Proj _) -> default ()

let recheck_against env sigma a b =
  let sigma, _, j = recheck_against env sigma a b in
  sigma, j.uj_type
