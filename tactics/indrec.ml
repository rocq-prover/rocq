(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* File initially created by Christine Paulin, 1996 *)

(* This file builds various inductive schemes *)

open CErrors
open Util
open Names
open Nameops
open Constr
open EConstr
open Declarations
open Context
open Vars
open Namegen
open Inductive
open Inductiveops
open Environ
open LibBinding
open State
open Retyping
open Context.Rel.Declaration

type dep_flag = bool

let ident_hd env ids t na =
  let na = named_hd env (Evd.from_env env) t na in
  next_name_away na ids

module RelEnv =
struct
  type t = { env : Environ.env; avoid : Id.Set.t }

  let make env =
    let avoid = Id.Set.of_list (Termops.ids_of_rel_context (rel_context env)) in
    { env; avoid }

  let avoid_decl avoid decl = match get_name decl with
  | Anonymous -> avoid
  | Name id -> Id.Set.add id avoid

  let push_rel decl env =
    { env = EConstr.push_rel decl env.env; avoid = avoid_decl env.avoid decl }

  let push_rel_context ctx env =
    let avoid = List.fold_left avoid_decl env.avoid ctx in
    { env = EConstr.push_rel_context ctx env.env; avoid }

end

let (!!) env = env.RelEnv.env

let set_names env l =
  let ids = env.RelEnv.avoid in
  let fold d (ids, l) =
    let id = ident_hd !!env ids (get_type d) (get_name d) in
    (Id.Set.add id ids, set_name (Name id) d :: l)
  in
  snd (List.fold_right fold l (ids,[]))

let make_name env s r =
  let id = next_ident_away (Id.of_string s) env.RelEnv.avoid in
  make_annot (Name id) r


(**********************************************************************)
(* Building case analysis schemes *)
(* Christine Paulin, 1996 *)

type case_analysis = {
  case_params : EConstr.rel_context;
  case_pred : Name.t EConstr.binder_annot * EConstr.types;
  case_branches : EConstr.rel_context;
  case_arity : EConstr.rel_context;
  case_body : EConstr.t;
  case_type : EConstr.t;
}

let eval_case_analysis case =
  let open EConstr in
  let body = it_mkLambda_or_LetIn case.case_body case.case_arity in
  (* Expand let bindings in the type for backwards compatibility *)
  let bodyT = it_mkProd_wo_LetIn case.case_type case.case_arity in
  let body = it_mkLambda_or_LetIn body case.case_branches in
  let bodyT = it_mkProd_or_LetIn bodyT case.case_branches in
  let (nameP, typP) = case.case_pred in
  let body = mkLambda (nameP, typP, body) in
  let bodyT = mkProd (nameP, typP, bodyT) in
  let c = it_mkLambda_or_LetIn body case.case_params in
  let cT = it_mkProd_or_LetIn bodyT case.case_params in
  (c, cT)

(* [p] is the predicate and [cs] a constructor summary *)
let build_branch_type env sigma dep p cs =
  let open EConstr in
  let open EConstr.Vars in
  let base = mkApp (lift cs.cs_nargs p, cs.cs_concl_realargs) in
  if dep then
    Namegen.it_mkProd_or_LetIn_name env sigma
      (applist (base,[build_dependent_constructor cs]))
      cs.cs_args
  else
    it_mkProd_or_LetIn base cs.cs_args

let paramdecls_fresh_template sigma (mib,u) =
  match mib.mind_template with
  | None ->
    let params = Inductive.inductive_paramdecls (mib, EConstr.EInstance.kind sigma u) in
    sigma, EConstr.of_rel_context params
  | Some templ ->
    assert (EConstr.EInstance.is_empty u);
    let sigma, univs = List.fold_left_map (fun sigma -> function
        | None -> sigma, (fun ~default -> assert false)
        | Some s ->
          let sigma, u = match snd (Inductive.Template.bind_kind s) with
            | None -> sigma, Univ.Universe.type0
            | Some _ ->
              let sigma, u = Evd.new_univ_level_variable UState.univ_rigid sigma in
              sigma, Univ.Universe.make u
          in
          sigma, fun ~default -> Inductive.TemplateUniv u)
        sigma
        templ.template_param_arguments
    in
    let csts, params, _ = Inductive.instantiate_template_universes mib univs in
    let sigma = Evd.add_constraints sigma csts in
    sigma, EConstr.of_rel_context params

let mis_make_case_com dep env sigma (ind, u as pind) (mib, mip) s =
  let open EConstr in
  let sigma = check_valid_elimination env sigma pind ~dep s in
  let sigma, lnamespar = paramdecls_fresh_template sigma (mib, u) in
  let indf = make_ind_family(pind, Context.Rel.instance_list mkRel 0 lnamespar) in
  let constrs = get_constructors env indf in
  let projs = get_projections env ind in
  let relevance = Retyping.relevance_of_sort s in
  let ndepar = mip.mind_nrealdecls + 1 in

  (* Pas génant car env ne sert pas à typer mais juste à renommer les Anonym *)
  (* mais pas très joli ... (mais manque get_sort_of à ce niveau) *)
  let env = RelEnv.make env in
  let env' = RelEnv.push_rel_context lnamespar env in

  let typP = make_arity !!env' sigma dep indf s in
  let nameP = make_name env' "P" ERelevance.relevant in

  let rec get_branches env k accu =
    if Int.equal k (Array.length mip.mind_consnames) then accu
    else
      let cs = lift_constructor (k+1) constrs.(k) in
      let t = build_branch_type !!env sigma dep (mkRel (k+1)) cs in
      let branch_name = make_annot (Name cs.cs_name) relevance in
      let decl = LocalAssum (branch_name, t) in
      get_branches (RelEnv.push_rel decl env) (k + 1) (decl :: accu)
  in

  let env' = RelEnv.push_rel (LocalAssum (nameP,typP)) env' in
  let branches = get_branches env' 0 [] in

  let arity, body, bodyT =
    let env = RelEnv.push_rel_context branches env' in
    let nbprod = Array.length mip.mind_consnames + 1 in

    let indf' = lift_inductive_family nbprod indf in
    let arsign = get_arity !!env indf' in
    let r = Inductiveops.relevance_of_inductive_family !!env indf' in
    let depind = build_dependent_inductive !!env indf' in
    let deparsign = LocalAssum (make_annot Anonymous r,depind) :: arsign in

    let ci = make_case_info !!env (fst pind) RegularStyle in
    let pbody =
      mkApp
        (mkRel (ndepar + nbprod),
          if dep then Context.Rel.instance mkRel 0 deparsign
          else Context.Rel.instance mkRel 1 arsign) in
    let deparsign = set_names env deparsign in
    let pctx =
      if dep then deparsign
      else LocalAssum (make_annot Anonymous r, depind) :: List.tl deparsign
    in
    let obj, objT =
      match projs with
      | None ->
        let pms = Context.Rel.instance mkRel (ndepar + nbprod) lnamespar in
        let iv =
          if Typeops.should_invert_case !!env (ERelevance.kind sigma relevance) ci then
            CaseInvert { indices = Context.Rel.instance mkRel 1 arsign }
          else NoInvert
        in
        let ncons = Array.length mip.mind_consnames in
        let mk_branch i =
          (* we need that to get the generated names for the branch *)
          let ft = get_type (lookup_rel (ncons - i) !!env) in
          let (ctx, _) = EConstr.decompose_prod_decls sigma ft in
          let brnas = Array.of_list (List.rev_map get_annot ctx) in
          let n = mkRel (List.length ctx + ndepar + ncons - i) in
          let args = Context.Rel.instance mkRel 0 ctx in
          (brnas, mkApp (n, args))
        in
        let br = Array.init ncons mk_branch in
        let pnas = Array.of_list (List.rev_map get_annot pctx) in
        let obj = mkCase (ci, u, pms, ((pnas, liftn ndepar (ndepar + 1) pbody), relevance), iv, mkRel 1, br) in
        obj, pbody
      | Some ps ->
        let term =
          mkApp (mkRel 2,
                  Array.map
                    (fun (p,r) ->
                       let r = EConstr.Vars.subst_instance_relevance u (ERelevance.make r) in
                       mkProj (Projection.make p true, r, mkRel 1))
                    ps)
        in
        if dep then
          let ty = mkApp (mkRel 3, [| mkRel 1 |]) in
          mkCast (term, DEFAULTcast, ty), ty
        else
          term, mkRel 3
    in
    (deparsign, obj, objT)
  in
  let params = set_names env lnamespar in
  let case = {
    case_params = params;
    case_pred = (nameP, typP);
    case_branches = branches;
    case_arity = arity;
    case_body = body;
    case_type = bodyT;
  } in
  (sigma, case)

(**********************************************************************)
(* This builds elimination predicate for Case tactic *)

let build_case_analysis_scheme env sigma pity dep kind =
  let specif = lookup_mind_specif env (fst pity) in
  mis_make_case_com dep env sigma pity specif kind

let prop_but_default_dependent_elim =
  Summary.ref ~name:"prop_but_default_dependent_elim" Indset_env.empty

let inPropButDefaultDepElim : inductive -> Libobject.obj =
  Libobject.declare_object @@
  Libobject.superglobal_object "prop_but_default_dependent_elim"
    ~cache:(fun i ->
        prop_but_default_dependent_elim := Indset_env.add i !prop_but_default_dependent_elim)
    ~subst:(Some (fun (subst,i) -> Mod_subst.subst_ind subst i))
    ~discharge:(fun i -> Some i)

let declare_prop_but_default_dependent_elim i =
  Lib.add_leaf (inPropButDefaultDepElim i)

let is_prop_but_default_dependent_elim i = Indset_env.mem i !prop_but_default_dependent_elim

let pseudo_sort_quality_for_elim ind mip =
  let s = mip.mind_sort in
  if Sorts.is_prop s && is_prop_but_default_dependent_elim ind
  then Sorts.Quality.qtype
  else Sorts.quality s

let is_in_prop mip =
  let s = mip.mind_sort in
  Sorts.is_prop s

let default_case_analysis_dependence env ind =
  let _, mip as specif = lookup_mind_specif env ind in
  Inductiveops.has_dependent_elim specif
  && (not (is_in_prop mip) || is_prop_but_default_dependent_elim ind)

let build_case_analysis_scheme_default env sigma pity kind =
  let dep = default_case_analysis_dependence env (fst pity) in
  build_case_analysis_scheme env sigma pity dep kind






(* ************************************************************************** *)
(*                             Generate Eliminators                           *)
(* ************************************************************************** *)

let (let@) x f = x f
let (let*) x f = State.bind x f

type elim_info = int * one_inductive_body * bool * Evd.esorts

let dbg = CDebug.create ~name:"generate_eliminators" ()

(* ************************************************************************** *)
(*                              View Argument                                 *)
(* ************************************************************************** *)

type arg =
  (* pos_ind, constant context, inst_nuparams inst_indices *)
  | ArgIsInd of int * rel_context * constr array * constr array
  (* kn_nested, pos_nested, inst_uparams, inst_nuparams_indices *)
  | ArgIsNested of MutInd.t * int
                   * mutual_inductive_body * one_inductive_body
                   * rel_context * constr array * constr array
  (* constant context, hd, args (maybe empty) *)
  | ArgIsCst of rel_context * constr * constr array

(* Decompose the argument in [it_Prod_or_LetIn local, X] where [X] is Ind, nested or a constant *)
let view_arg kn mdecl t : arg State.t =
  let* (cxt, hd) = whd_decompose_prod_decls t in
  let* (hd, iargs) = decompose_app hd in
  let* sigma = get_sigma in
  match kind sigma hd with
  | Ind ((kn_ind, pos_ind), _) ->
    (* If it is the inductive *)
    if kn = kn_ind
    then let (_, local_nuparams_indices) = Array.chop mdecl.mind_nparams_rec iargs in
         let (local_nuparams, local_indices) = Array.chop (mdecl.mind_nparams - mdecl.mind_nparams_rec) local_nuparams_indices in
         return @@ ArgIsInd (pos_ind, cxt, local_nuparams, local_indices)
    (* if there is no argument, it cannot be nested *)
    else if Array.length iargs = 0 then return @@ ArgIsCst (cxt, hd, iargs)
    else begin
      (* If it may be nested *)
      let* env = get_env in
      let (mib_nested, ind_nested) = lookup_mind_specif env (kn_ind, pos_ind) in
      let (inst_uparams, inst_nuparams_indices) = Array.chop mib_nested.mind_nparams_rec iargs in
      return @@ ArgIsNested (kn_ind, pos_ind, mib_nested, ind_nested, cxt, inst_uparams, inst_nuparams_indices)
      end
  | _ -> return @@ ArgIsCst (cxt, hd, iargs)

let warn_no_sparse_parametricity =
  CWarnings.create ~name:"no-sparse-parametricity" ~category:Deprecation.Version.v9_2
  Pp.(fun (ind, ind_nested) ->
    Nametab.XRefs.pr (TrueGlobal (IndRef ind)) ++ str " is nested using " ++  Nametab.XRefs.pr (TrueGlobal (IndRef ind_nested)) ++
    str " but sparse parametricity for " ++ Nametab.XRefs.pr (TrueGlobal (IndRef ind_nested)) ++ str " is not registered.\n"
    )

let warn_no_local_fundamental_theorem =
  CWarnings.create ~name:"no-local_fundamental_theorem" ~category:Deprecation.Version.v9_2
  Pp.(fun (ind,ind_nested) ->
    Nametab.XRefs.pr (TrueGlobal (IndRef ind)) ++ str " is nested using " ++  Nametab.XRefs.pr (TrueGlobal (IndRef ind_nested)) ++
    str " but the local fundamental theorem for " ++ Nametab.XRefs.pr (TrueGlobal (IndRef ind_nested)) ++ str " is not registered.\n"
    )

let lookup_parametricity ind ind_nested =
    match Ind_tables.lookup_scheme "sparse_parametricity" ind_nested with
    | None -> warn_no_sparse_parametricity (ind, ind_nested); None
    | Some ref_sparam ->
    match Ind_tables.lookup_scheme "local_fundamental_theorem" ind_nested with
    | None -> warn_no_local_fundamental_theorem (ind, ind_nested); None
    | Some ref_lfth -> Some (ref_sparam, ref_lfth)

let get_params_sep sigma mdecl u =
  let (sigma, up_params) = paramdecls_fresh_template sigma (mdecl, u) in
  let (uparams, nuparams) = Declareops.split_uparans_nuparams mdecl.mind_nparams_rec up_params in
  (sigma, uparams, nuparams)

let closure_uparams binder s uparams = closure_context_sep binder Old s uparams
let closure_nuparams binder s nuparams = closure_context_sep binder Old s nuparams

(* get the position in ind_bodies out of the position of mind_packets *)
let find_opt_pos p l =
  let rec aux i l = match l with
  | [] -> None
  | h::_ when p h -> Some (i, h)
  | _::t -> aux (1+i) t
  in aux 0 l

(* Closure for indices must be fresh as it is not in the context of the arguments *)
let closure_indices binder naming_scheme indb u f =
  let* i = get_indices indb u in
  closure_context_sep binder Fresh naming_scheme i f

(* Convention for comments:
  - A1 ... An : uniform parameters = uparams
  - B0 ... Bm : non-uniform parameters = nuparams
  - i0 ... il : indices
*)

(* Builds the type of the predicate for the i-th block
    forall (B0 ... Bm : nuparams),
    forall (i1 ... tl : indices),
    (Ind A1 ... An B0 ... Bm i1 ... il) -> U)  *)
let make_type_pred kn u (pos_ind, ind, dep, sort) key_uparams nuparams =
  let@ (key_nuparams, _, _) = closure_nuparams Prod naming_hd_fresh nuparams in
  let@ (key_indices , _, _) = closure_indices  Prod (naming_hd_fresh_dep dep) ind u in
  (* NOT DEP: return the sort *)
  if not dep then return @@ mkSort sort else
  (* DEP: bind the inductive, and return the sort *)
  let* rev_ind = ind_relevance ind u in
  let name_ind = make_annot Anonymous rev_ind in
  let* tind = make_ind ((kn, pos_ind), u) key_uparams key_nuparams key_indices in
  let@ _ = make_binder Prod naming_hd_fresh name_ind tind in
  return @@ mkSort sort

(* Closure Predicates *)
let closure_preds kn u ind_bodies binder key_uparams nuparams cc =
  fold_right_state (fun a l -> a :: l) ind_bodies (fun _ ind cc ->
    let name_pred = make_annot (Name (Id.of_string "P")) ERelevance.relevant in
    let* ty_pred = make_type_pred kn u ind key_uparams nuparams in
    make_binder binder naming_hd_fresh name_pred ty_pred cc
  ) cc

let mkFunTrue x =
  (* rebind the lambdas, and recover the head *)
  let* (cxt, hd) = decompose_lambda_decls x in
  let@ _ = closure_context Lambda Fresh naming_id cxt in
  (* bind the head *)
  let* sort = retyping_sort_of hd in
  let rev_x = relevance_of_sort sort in
  let name_var = make_annot Anonymous rev_x in
  let@ _ = make_binder Lambda naming_id name_var hd in
  (* return [True] *)
  return @@ mkRef ((Rocqlib.lib_ref "core.True.type"), EInstance.empty)

let instantiate_sparam inst_uparams strpos preds =
  let preds = Array.to_list preds in
  let inst_uparams = Array.to_list inst_uparams in
  let* s = get_state in
  let inst_sparam =
    List.fold_right (fun (inst_uparam, b, pred) acc ->
      if not b then inst_uparam :: acc
      else match pred with
      | None -> inst_uparam :: (snd @@ mkFunTrue inst_uparam s) :: acc
      | Some pred -> inst_uparam :: pred :: acc
      )
    (List.combine3 inst_uparams strpos preds) []
  in
  return @@ Array.of_list inst_sparam

(* Recursively compute the predicate, returns None if it is not nested *)
let compute_pred f i x : (constr option) t = begin
  (* quantify local variables *)
  let* (cxt, hd) = decompose_lambda_decls x in
  let@ (key_loc, _, _) = closure_context_sep_opt Lambda Fresh naming_id cxt in
  (* create new variable *)
  let* sort = retyping_sort_of hd in
  let rev_x = relevance_of_sort sort in
  let name_var = make_annot Anonymous rev_x in
  (* let name_var = make_annot Anonymous ERelevance.relevant in *)
  let@ key_arg = make_binder_opt Lambda naming_id name_var hd in
  let* ty_var = State.get_type key_arg in
  (* compute rec call *)
  let* res = f key_arg ty_var in
  return @@ res
  end

(* This function computes the type of the recursive call *)
let rec make_rec_call_ty kn pos_ind mdecl ind_bodies key_preds key_arg ty : (ERelevance.t * constr) option t =
  let* v = view_arg kn mdecl ty in
  match v with
  | ArgIsInd (pos_ind_block, loc, inst_nuparams, inst_indices) ->
    begin
      (* generate recursion hypotheses only for the blocks that are used *)
      match find_opt_pos (fun (i,_,_,_) -> i = pos_ind_block) ind_bodies with
      | None -> return None
      | Some (pred_pos, (_, _, pred_dep, sort)) ->
          let rec_hyp =
            let@ (key_locals, _, _) = closure_context_sep Prod Fresh naming_id loc in
            let* pred = geti_term key_preds pred_pos in
            let pred = mkApp (pred, (Array.append inst_nuparams inst_indices)) in
            (* NOT DEP: return the predicate *)
            if not pred_dep then return pred else
            (* DEP: Apply the predicate to the argument*)
            let* arg = get_term key_arg in
            let* loc = get_terms key_locals in
            (* Pi B0 ... Bm i0 ... il (x a0 ... an) *)
            return @@ mkApp (pred, [| mkApp (arg , loc) |])
          in
          let* rec_hyp = rec_hyp in
          return (Some (relevance_of_sort sort, rec_hyp))
    end
  | ArgIsNested (kn_nested, pos_nested, mib_nested, ind_nested,
                  loc, inst_uparams, inst_nuparams_indices) ->
    begin
      let@ (key_locals, _, _) = closure_context_sep_opt_prod Prod Old naming_id loc in
      (* eta expand arguments *)
      let uparams_nested = of_rel_context @@ fst @@ Declareops.split_uparans_nuparams mib_nested.mind_nparams_rec mib_nested.mind_params_ctxt in
      let* inst_uparams = eta_expand_instantiation inst_uparams uparams_nested in
      (* Compute the recursive predicates *)
      let compute_pred i x = compute_pred (fun a b -> State.map (fun x -> Option.map snd x) @@ make_rec_call_ty kn pos_ind mdecl ind_bodies key_preds a b) i x in
      let* rec_preds = array_mapi compute_pred inst_uparams in
      (* If at least one argument is nested, lookup the sparse parametricity *)
      if Array.for_all Option.is_empty rec_preds then return None else begin
      match lookup_parametricity (kn, pos_ind) (kn_nested, pos_nested) with
      | None -> return None
      | Some (ref_sparam, _) ->
      (* Create: Indε A0 PA0 ... An PAn B0 ... Bm i0 ... il (arg a0 ... an) *)
      let* ref_ind = fresh_global ref_sparam in
      let* inst_uparams = instantiate_sparam inst_uparams mib_nested.mind_params_rec_strpos rec_preds in
        (* arg a0 ... an *)
      let* arg = get_term key_arg in
      let* loc = get_terms key_locals in
      let arg = mkApp (arg , loc) in
        (* Instantiation *)
      let* rec_hyp = typing_checked_appvect ref_ind @@ Array.concat [inst_uparams; inst_nuparams_indices; [|arg|]] in
      (* Compute the relevance after the instantiation *)
      let* rec_hyp_sort = retyping_sort_of rec_hyp in
      let rec_hyp_rev = relevance_of_sort rec_hyp_sort in
      (* return *)
      return (Some (rec_hyp_rev, rec_hyp))
      end
    end
  | _ -> return None

(* Create and bind the recursive call *)
let make_rec_call_cc kn pos_ind mdecl ind_bodies key_preds _ key_arg cc =
  let* arg = LibBinding.State.get_type key_arg in
  let* rec_call = make_rec_call_ty kn pos_ind mdecl ind_bodies key_preds key_arg arg in
  match rec_call with
  | Some (rec_hyp_rev, rec_hyp_ty) ->
      let name_rec_hyp = make_annot Anonymous rec_hyp_rev in
      let@ _ = make_binder Prod naming_id name_rec_hyp rec_hyp_ty in
      cc [key_arg]
  | _ -> cc [key_arg]

(* Generates the type associated to a constructor *)
(* forall (B0 ... Bm : nuparams),
    forall x0 : arg0, [P x0], ..., xn : argn, [P n],
    P B0 ... Bm f0 ... fl (cst A0 ... An B0 ... Bm x0 ... xl) *)
let make_type_ctor kn u mdecl ind_bodies pos_list (pos_ind, ind, dep, sort) pos_ctor ctor key_uparams nuparams key_preds =
  let@ (key_nuparams, _, _) = closure_nuparams Prod naming_id nuparams in
  let (args, indices) = ctor in
  (* bind the arguments of the constructor and the recursive hypotheses, if any *)
  let@ key_args = read_by_decl args (build_binder Prod Old (naming_hd_dep dep))
                        (fun _ _ cc -> cc []) (make_rec_call_cc kn pos_ind mdecl ind_bodies key_preds) in
  (* P B0 ... Bm f0 ... fl (cst A0 ... An B0 ... Bm x0 ... xl) *)
  let* pred = geti_term key_preds pos_list in
  let* nuparams = get_terms key_nuparams in
  let* indices = array_mapi (fun _ -> weaken) indices in
  let pred = mkApp (pred, Array.concat [nuparams; indices]) in
  (* NOT DEP: return the predicate *)
  if not dep then return pred else
  (* DEP: return the predicate applied to the constructor *)
  let* args = get_terms key_args in
  let* cst = make_cst ((kn, pos_ind), u) pos_ctor key_uparams key_nuparams args in
  return @@ mkApp (pred, [| cst |])

(* closure assumptions functions over all the ctors *)
let closure_ctors kn mdecl u ind_bodies binder key_uparams nuparams key_preds =
  fold_right_state (fun a l -> a :: l) ind_bodies (
    fun pos_list (pos_ind, ind, dep, sort) cc ->
    iterate_ctors mdecl ind u (
      fun pos_ctor ctor cc ->
      let name_assumption = make_annot (Name ind.mind_consnames.(pos_ctor)) (relevance_of_sort sort) in
      let* fct = make_type_ctor kn u mdecl ind_bodies pos_list (pos_ind, ind, dep, sort) pos_ctor ctor key_uparams nuparams key_preds in
      make_binder binder naming_hd_fresh name_assumption fct cc
    ) cc
  )

(* Make the type of the conclusion *)
(* P B0 ... Bm i0 ... il x *)
let make_ccl key_preds focus dep key_nuparams key_indices key_VarMatch =
  let* pred = geti_term key_preds focus in
  let* nuparams_indices = get_terms (key_nuparams @ key_indices) in
  let pred = mkApp (pred, nuparams_indices) in
  (* NOT DEP: return the predicate *)
  if not dep then return pred else
  (* DEP: return the predicate applied to the variable *)
  let* var = get_term key_VarMatch in
  return @@ mkApp (pred, [| var |])

(* Make the return type *)
(* forall (B0 ... Bm : nuparams),
    forall (i1 ... il : indices),
    forall (x : Ind A0 ... An B0 ... Bm i0 ... il),
    P B0 ... Bm i0 ... il x *)
let make_return_type kn u ind_bodies focus key_uparams nuparams key_preds =
  let (pos_ind, ind, dep, sort) = List.nth ind_bodies focus in
  let@ (key_nuparams, _, _) = closure_nuparams Prod naming_hd_fresh nuparams in
  let@ (key_indices , _, _) = closure_indices Prod naming_hd_fresh ind u in
  let* rev_ind = ind_relevance ind u in
  let name_ind = make_annot Anonymous rev_ind in
  let* tind = make_ind ((kn, pos_ind), u) key_uparams key_nuparams key_indices in
  let@ (key_VarMatch) = make_binder Prod naming_hd_fresh name_ind tind in
  make_ccl key_preds focus dep key_nuparams key_indices key_VarMatch

(** Generate the type of the recursor, useful for debugging *)
let _gen_elim_type print_constr kn u mdecl uparams nuparams (ind_bodies : elim_info list) (focus : int) =

  dbg Pp.(fun () -> str "\n------------------------------------------------------------- \n"
    ++ str "DEBUBG TYPE: " ++ str (MutInd.to_string kn) ++ str " ## pos_ind : " ++ str (string_of_int focus) ++ str "\n") ;

  let t =
    let@ (key_uparams, _, _) = closure_uparams Prod naming_hd_fresh uparams in
    let@ key_preds = closure_preds kn u ind_bodies Prod key_uparams nuparams in
    let@ key_ctors = closure_ctors kn mdecl u ind_bodies Prod key_uparams nuparams key_preds in
    make_return_type kn u ind_bodies focus key_uparams nuparams key_preds
  in

  fun s -> let (sigma, t) = t s in
  dbg Pp.(fun () -> print_constr (snd @@ get_env s) sigma t ++ str "\n");
  (sigma, t)


(* Create the body of the eliminators *)

let mkFunI x =
  (* rebind the lambdas, and recover the head *)
  let* (cxt, hd) = decompose_lambda_decls x in
  let@ _ = closure_context_sep Lambda Fresh naming_id cxt in
  (* bind the head *)
  let* sort = retyping_sort_of hd in
  let rev_x = relevance_of_sort sort in
  let name_var = make_annot Anonymous rev_x in
  let@ key_arg = make_binder Lambda naming_id name_var hd in
  (* return I *)
  return @@ mkRef ((Rocqlib.lib_ref "core.True.I"), EInstance.empty)

let instantiate_fundamental_theorem inst_uparams strpos preds preds_hold =
  let inst_uparams = Array.to_list inst_uparams in
  let preds = Array.to_list preds in
  let preds_hold = Array.to_list preds_hold in
  let* s = get_state in
  let inst_lfth =
    List.fold_right (fun (inst_uparam, b, (pred, pred_hold)) acc ->
      if not b then inst_uparam :: acc
      else match pred, pred_hold with
      | None, None -> inst_uparam :: (snd @@ mkFunTrue inst_uparam s) :: (snd @@ mkFunI inst_uparam s) :: acc
      | Some pred, Some pred_hold -> inst_uparam :: pred :: pred_hold :: acc
      | _, _ -> assert false
    )
    (List.combine3 inst_uparams strpos @@ List.combine preds preds_hold) []
  in
  return @@ Array.of_list inst_lfth

(* ty is well-formed in s *)
let rec make_rec_call kn pos_ind mdecl ind_bodies key_preds key_fixs key_arg ty : (constr option) State.t =
  let* v = view_arg kn mdecl ty in
  match v with
  | ArgIsInd (pos_ind_block, loc, inst_nuparams, inst_indices) -> begin
    (* generate recursion hypotheses only for the blocks that are used *)
      match find_opt_pos (fun (i,_,_,_) -> i = pos_ind_block) ind_bodies with
      | None -> return None
      | Some (pred_pos, _) ->
        (* Fi B0 ... Bm i0 ... il (x a0 ... an) *)
        let@ (key_locals, _, _) = closure_context_sep_opt Lambda Fresh naming_id loc in
        let* pred = geti_term key_fixs pred_pos in
        let pred = mkApp (pred, Array.concat [inst_nuparams; inst_indices]) in
        let* arg = get_term key_arg in
        let* loc = get_terms key_locals in
        return @@ Some (mkApp (pred, [| mkApp (arg, loc) |]))
    end
  | ArgIsNested (kn_nested, pos_nested, mib_nested, ind_nested,
                  loc, inst_uparams, inst_nuparams_indices) ->
    begin
      let@ (key_locals, _, _) = closure_context_sep_opt Lambda Old naming_id loc in
      (* eta expand arguments *)
      let uparams_nested = of_rel_context @@ fst @@ Declareops.split_uparans_nuparams mib_nested.mind_nparams_rec mib_nested.mind_params_ctxt in
      let* inst_uparams = eta_expand_instantiation inst_uparams uparams_nested in
      (* Compute the recursive predicates, and their proofs *)
      let compute_pred_preds = compute_pred (fun a b -> State.map (fun x -> Option.map snd x) @@ make_rec_call_ty kn pos_ind mdecl ind_bodies key_preds a b) in
      let* rec_preds = array_mapi compute_pred_preds inst_uparams in
      let compute_pred_holds = compute_pred (make_rec_call kn pos_ind mdecl ind_bodies key_preds key_fixs) in
      let* rec_preds_hold = array_mapi compute_pred_holds inst_uparams in
      (* If at least one argument is nested, lookup the local fundamental theorem *)
      if Array.for_all Option.is_empty rec_preds_hold then return None else begin
      match lookup_parametricity (kn, pos_ind) (kn_nested, pos_nested) with
      | None -> return None
      | Some (_, ref_fth) ->
      (* fth A0 PA0 HPA0 ... An PAn HPAn B0 ... Bm i0 ... il (arg a0 ... an) *)
      let* fth = fresh_global ref_fth in
      let* inst_uparams = instantiate_fundamental_theorem inst_uparams mib_nested.mind_params_rec_strpos rec_preds rec_preds_hold in
        (* arg a0 ... an *)
      let* arg = get_term key_arg in
      let* loc = get_terms key_locals in
      let arg = mkApp (arg , loc) in
        (* Instantiation *)
      let* rec_hyp = typing_checked_appvect fth (Array.concat [inst_uparams; inst_nuparams_indices; [|arg|] ]) in
      return @@ Some (rec_hyp)
      end
    end
  | _ -> return None

(* Compute the arguments of the rec call *)
let compute_args_fix kn pos_ind mdecl ind_bodies pos_list key_preds key_fixs key_args =
  CList.fold_right_i (fun pos_arg key_arg acc ->
    let* acc = acc in
    let* tm_arg = get_term key_arg in
    let* ty_arg = State.get_type key_arg in
    let* rec_call = make_rec_call kn pos_ind mdecl ind_bodies key_preds key_fixs key_arg ty_arg in
    match rec_call with
      | Some rc_tm -> return @@ tm_arg :: rc_tm :: acc
      | None -> return @@ tm_arg :: acc
  ) 0 key_args (return [])

let _gen_elim print_constr kn u mdecl uparams nuparams (ind_bodies : elim_info list) (focus : int) =

  dbg Pp.(fun () -> str "\n------------------------------------------------------------- \n"
    ++ str "DEBUBG TERM: " ++ str (MutInd.to_string kn) ++ str " ## pos_ind : " ++ str (string_of_int focus) ++ str "\n") ;

  let t =

  (* 1. Closure Uparams / preds / ctors *)
  let@ (key_uparams, _, _) = closure_uparams Lambda naming_hd_fresh uparams in
  let@ key_preds = closure_preds kn u ind_bodies Lambda key_uparams nuparams in
  let@ key_ctors = closure_ctors kn mdecl u ind_bodies Lambda key_uparams nuparams key_preds in
  (* 2. Fixpoint *)
  let fix_name pos_list (_,_,_,sort) = make_annot (Name (Id.of_string "F")) (relevance_of_sort sort) in
  let fix_type pos_list _ = make_return_type kn u ind_bodies pos_list key_uparams nuparams key_preds in
  let fix_rarg pos_list (_,ind,_,_) = (mdecl.mind_nparams - mdecl.mind_nparams_rec) + ind.mind_nrealargs in
  (* Compute if it is recursive *)
  let* is_rec =
    let* env = get_env in
    let (_, ind, _, _) = List.hd ind_bodies in
    return @@ (List.length ind_bodies > 1 || Inductiveops.mis_is_recursive env ((kn, focus), mdecl, ind)) in
  (* Create a fix only if it is recursive or has more than one inductive body *)
  let@ (key_fixs, pos_list, (pos_ind, ind, dep, sort)) =
    if is_rec
    then make_fix ind_bodies focus fix_rarg fix_name fix_type
    else fun cc -> cc ([], 0, List.hd ind_bodies) in
  (* 3. Closure Nuparams / Indices / Var *)
  let@ (key_nuparams, _, _) = closure_nuparams Lambda naming_hd_fresh nuparams in
  let@ (key_indices , _, _) = closure_indices Lambda naming_hd_fresh ind u in
  let* rev_ind = ind_relevance ind u in
  let name_ind = make_annot Anonymous rev_ind in
  let* tind = make_ind ((kn, pos_ind), u) key_uparams key_nuparams key_indices in
  let@ key_VarMatch = make_binder Lambda naming_hd_fresh name_ind tind in
  let ccl =
  (* 4 Match to prove P ... x *)
    let* params = get_terms (key_uparams @ key_nuparams )in
    let case_pred = make_ccl key_preds pos_list dep key_nuparams in
    let* var_match = get_term key_VarMatch in
    let* indices = get_terms key_indices in
    let@ (key_args, _, _, pos_ctor) =
      make_case_or_projections naming_hd_fresh mdecl (kn, pos_ind) ind u key_uparams key_nuparams params
        indices case_pred (relevance_of_sort sort) var_match in
    (* 5 Body of the branch *)
    let* hyp = getij_term key_ctors pos_list pos_ctor in
    let* nuparams = get_terms key_nuparams in
    let* cfix = compute_args_fix kn pos_ind mdecl ind_bodies pos_list key_preds key_fixs key_args in
    typing_checked_appvect hyp (Array.concat [nuparams; Array.of_list cfix])
  in
  (* 6. If it is not-recursive, has primitive projections and is dependent => add a cast *)
  let* env = get_env in
  let projs = Environ.get_projections env (kn, pos_ind) in
  if is_rec || Option.is_empty projs || not dep
  then ccl
  else
    let* ty = make_ccl key_preds pos_list dep key_nuparams key_indices key_VarMatch in
    let* ccl = ccl in
    return @@ mkCast (ccl, DEFAULTcast, ty)

  in
  fun s -> let (sigma, t) = t s in
  dbg Pp.(fun () -> print_constr (snd @@ get_env s) sigma t ++ str "\n");
  (sigma, t)


(**********************************************************************)
(* build the eliminators mutual and individual *)

(* Check all dependent eliminations are allowed*)
let check_elim env sigma (kn, n) mib u lrecspec =
  List.iter (fun ((kni, ni),dep,s) ->
    (* Check that all the blocks can be eliminated to s *)
    let elim_allowed = Array.fold_right (fun mipi b -> b && Inductiveops.is_allowed_elimination sigma ((mib,mipi),u) s) mib.mind_packets true in
    if not elim_allowed
    then raise (RecursionSchemeError (env, NotAllowedCaseAnalysis (sigma, true, ESorts.kind sigma s, ((kn, ni), EInstance.kind sigma u))));
    (* Check if dep elim is allowed: rec (co)ind records with prim proj can not be eliminated dependently *)
    if dep && not (Inductiveops.has_dependent_elim (mib, mib.mind_packets.(ni)))
    then raise (RecursionSchemeError (env, NotAllowedDependentAnalysis (true, (kni, ni))));
  ) lrecspec

(* Check all the blocks are mutual, and not given twice *)
let check_mut env sigma (kn, n) mib u lrecspec =
  List.fold_left (fun ln ((kni, ni),dep,s) ->
    (* Check al the block are mutual  *)
    if not (QMutInd.equal env kn kni)
    then raise (RecursionSchemeError (env, NotMutualInScheme ((kn, n),(kni, ni))));
    (* Check none is given twice *)
    if Int.List.mem ni ln
    then raise (RecursionSchemeError (env, DuplicateInductiveBlock (kn, ni)))
    else ni::ln
  ) [n] lrecspec

let build_mutual_induction_scheme env sigma ?(force_mutual=false) lrecspec u =
  match lrecspec with
  | (mind,dep,s)::tail ->
      let mib, mip = lookup_mind_specif env mind in
      (* Check the blocks are all mutual, different, and can be eliminated dependently *)
      let _ = check_mut env sigma mind mib u tail in
      let _ = check_elim env sigma mind mib u lrecspec in
      (* Compute values for gen_elim *)
      let listdepkind = (snd mind, mip, dep, s) :: List.map (fun ((_,ni), dep, s) -> (ni, mib.mind_packets.(ni), dep, s)) tail in
      (* Get parameters, and generalized them for UnivPoly + TemplatePoly *)
      let (sigma, uparams, nuparams) = get_params_sep sigma mib u in
      (* Compute eliminators *)
      let elims =
          list_mapi (fun i _ -> _gen_elim Termops.Internal.print_constr_env (fst mind) u mib uparams nuparams listdepkind i)
                    (List.init (List.length listdepkind) (fun  _ -> 2))
      in
      run env sigma elims
  | _ -> anomaly (Pp.str "build_mutual_induction_scheme expects a non empty list of inductive types.")

let build_induction_scheme env sigma (ind, u) dep kind =
  on_snd List.hd @@ build_mutual_induction_scheme env sigma [(ind, dep, kind)] u
