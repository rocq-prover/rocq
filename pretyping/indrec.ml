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

open Pp
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

(* Errors related to recursors building *)
type recursion_scheme_error =
  | NotAllowedCaseAnalysis of Evd.evar_map * (*isrec:*) bool * Sorts.t * pinductive
  | NotMutualInScheme of inductive * inductive
  | DuplicateInductiveBlock of inductive
  | NotAllowedDependentAnalysis of (*isrec:*) bool * inductive

exception RecursionSchemeError of env * recursion_scheme_error

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


(*******************************************)
(* Building curryfied elimination          *)
(*******************************************)

let check_privacy_block specif =
  if Inductive.is_private specif then
    user_err (str"case analysis on a private inductive type")

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

let check_valid_elimination env sigma (ind, u as pind) ~dep s =
  let specif = Inductive.lookup_mind_specif env ind in
  let () =
    if dep && not (Inductiveops.has_dependent_elim specif) then
      raise (RecursionSchemeError (env, NotAllowedDependentAnalysis (false, ind)))
  in
  let () = check_privacy_block specif in
  match Inductiveops.make_allowed_elimination sigma (specif,u) s with
  | Some sigma -> sigma
  | None ->
    let s = EConstr.ESorts.kind sigma s in
    let pind = on_snd EConstr.Unsafe.to_instance pind in
    raise
      (RecursionSchemeError
         (env, NotAllowedCaseAnalysis (sigma, false, s, pind)))

let paramdecls_fresh_template sigma (mib,u) =
  match mib.mind_template with
  | None ->
    let params = Inductive.inductive_paramdecls (mib, EConstr.Unsafe.to_instance u) in
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
    let sigma = Evd.add_poly_constraints QGraph.Internal sigma csts in
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
(*                              Generate Recursors                            *)
(* ************************************************************************** *)

let (let@) x f = x f
let (let*) x f = fun s -> let a = x s in f a s

type elim_info = int * one_inductive_body * bool * Evd.esorts

let dbg = CDebug.create ~name:"generate_recursors" ()

(* ************************************************************************** *)
(*                              View Argument                                 *)
(* ************************************************************************** *)

type arg =
  (* pos_ind, constant context, inst_nuparams inst_indices *)
  | ArgIsInd of int * rel_context * constr array * constr array
  (* constant context, hd, args (maybe empty) *)
  | ArgIsCst of rel_context * constr * constr array

(* Decompose the argument in [it_Prod_or_LetIn local, X]
  where [X] is Ind, nested or a constant *)
let view_arg kname mdecl t : arg State.t =
  let* env = get_env in
  let* sigma = get_sigma in
  let (cxt, hd) = Reductionops.whd_decompose_prod_decls env sigma t in
  let (hd, iargs) = decompose_app sigma hd in
  match kind sigma hd with
  (* If it is nested *)
  | Ind ((kname_indb, pos_indb), _) ->
    (* If it is the inductive *)
    if kname = kname_indb
    then let (_, local_nuparams_indices) = Array.chop mdecl.mind_nparams_rec iargs in
         let (local_nuparams, local_indices) = Array.chop (mdecl.mind_nparams - mdecl.mind_nparams_rec) local_nuparams_indices in
         return @@ ArgIsInd (pos_indb, cxt, local_nuparams, local_indices)
    (* 2.2 If it is nested *)
    else if Array.length iargs = 0 then return @@ ArgIsCst (cxt, hd, iargs)
    else begin
      (* NESTED NOT TREATED FOR THE MOMENT *)
      return @@ ArgIsCst (cxt, hd, iargs)
      end
  | _ -> return @@ ArgIsCst (cxt, hd, iargs)

(* seperate uparams and nuparams *)
let chop_letin n l =
  let rec goto i acc = function
    | h :: t ->
      begin match h with
      | LocalAssum _ -> if Int.equal i 0 then (List.rev acc, h::t) else goto (pred i) (h :: acc) t
      | LocalDef _ -> goto i (h :: acc) t
      end
    | [] -> if Int.equal i 0 then (List.rev acc, []) else failwith "goto"
  in
  goto n [] l

let get_params_sep sigma mdecl u =
  let (sigma, up_params) = paramdecls_fresh_template sigma (mdecl, u) in
  let (uparams, nuparams) = chop_letin mdecl.mind_nparams_rec @@ List.rev up_params in
  (sigma, List.rev uparams, List.rev nuparams)

let closure_uparams binder s uparams = closure_context_sep binder Old s uparams
let closure_nuparams binder s nuparams = closure_context_sep binder Old s nuparams




(* get the position in ind_bodies out of the position of mind_packets *)
let find_opt_pos p l =
  let rec aux i l = match l with
  | [] -> None
  | h::_ when p h -> Some (i, h)
  | _::t -> aux (1+i) t
  in aux 0 l

(* relevance *)
let ind_relevance ind u = ERelevance.make @@ relevance_of_ind_body ind (EConstr.Unsafe.to_instance u)

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
  if not dep then return  @@ mkSort sort else
  (* DEP: bind the inductive, and return the sort *)
  let name_ind = make_annot Anonymous (ind_relevance ind u) in
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

(* This function computes the type of the recursive call *)
let make_rec_call kn mdecl ind_bodies key_preds key_arg ty =
  let* v = view_arg kn mdecl ty in
  match v with
  | ArgIsInd (pos_ind_block, loc, inst_nuparams, inst_indices) -> begin
      (* generate recursion hypotheses only for the blocks that are used *)
      match find_opt_pos (fun (i,_,_,_) -> i = pos_ind_block) ind_bodies with
      | None -> return None
      | Some (pred_pos, (_, _, pred_dep, sort)) -> return @@
      Some (
        relevance_of_sort sort,
        (* Pi B0 ... Bm i0 ... il (x a0 ... an) *)
        let@ (key_locals, _, _) = closure_context_sep Prod Fresh naming_id loc in
        let* i = geti_term key_preds pred_pos in
        let pred = mkApp (i, (Array.append inst_nuparams inst_indices)) in
        (* NOT DEP: return the predicate *)
        if not pred_dep then return pred else
        (* DEP: Apply the predicate to the argument *)
        let* arg = get_term key_arg in
        let* loc = get_terms key_locals in
        let arg = mkApp (arg , Array.of_list loc) in
        return @@ mkApp (pred, [| arg |])
      )
    end
  | _ -> return None

(* Create and bind the recursive call *)
let make_rec_call_cc kn mdecl ind_bodies key_preds _ key_arg cc =
  let* arg = LibBinding.State.get_type key_arg in
  let* rec_call = make_rec_call kn mdecl ind_bodies key_preds key_arg arg in
  match rec_call with
  | Some (rec_hyp_rev, rec_hyp_ty) ->
      let name_rec_hyp = make_annot Anonymous rec_hyp_rev in
      let* rec_hyp_ty = rec_hyp_ty in
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
  let@ key_args = read_by_decl args (build_binder Prod Old (naming_hd_dep dep))
                        (fun _ _ cc -> cc []) (make_rec_call_cc kn mdecl ind_bodies key_preds) in
  let* state = get_state in
  let weaken a = weaken a state in
  let indices = Array.map weaken indices in
  let* x = geti_term key_preds pos_list in
  let* y = get_terms key_nuparams in
  let pred = mkApp (x, Array.append (Array.of_list y) indices) in
  (* NOT DEP: return the predicate *)
  if not dep then return pred else
  (* DEP: return the predicate applied to the constructor *)
  let* k = get_terms key_args in
  let* cst = make_cst ((kn, pos_ind), u) pos_ctor key_uparams key_nuparams k in
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
  let* x = get_terms key_nuparams in
  let* y = get_terms key_indices in
  let args = Array.of_list (x @ y) in
  let* z = geti_term key_preds focus in
  let pred = mkApp (z, args) in
  if not dep then return pred else
  let* km = get_term key_VarMatch in
  return @@ mkApp (pred, [| km |])

(* Make the return type *)
(* forall (B0 ... Bm : nuparams),
    forall (i1 ... il : indices),
    forall (x : Ind A0 ... An B0 ... Bm i0 ... il),
    P B0 ... Bm i0 ... il x *)
let make_return_type kn u ind_bodies focus key_uparams nuparams key_preds =
  let (pos_ind, ind, dep, sort) = List.nth ind_bodies focus in
  let@ (key_nuparams, _, _) = closure_nuparams Prod naming_hd_fresh nuparams in
  let@ (key_indices , _, _) = closure_indices Prod naming_hd_fresh ind u in
  let name_ind = make_annot Anonymous (ind_relevance ind u) in
  let* tind = make_ind ((kn, pos_ind), u) key_uparams key_nuparams key_indices in
  let@ (key_VarMatch) = make_binder Prod naming_hd_fresh name_ind tind in
  make_ccl key_preds focus dep key_nuparams key_indices key_VarMatch

(* ty is well-formed in s *)
let make_rec_call kn mdecl ind_bodies key_fixs key_arg ty : ((constr State.t) option) State.t =
  let* v = view_arg kn mdecl ty in
  match v with
  | ArgIsInd (pos_ind_block, loc, inst_nuparams, inst_indices) -> begin
    (* generate recursion hypotheses only for the blocks that are used *)
      match find_opt_pos (fun (i,_,_,_) -> i = pos_ind_block) ind_bodies with
      | None -> return None
      | Some (pred_pos, _) ->
      return @@ Some (
        (* Fi B0 ... Bm i0 ... il (x a0 ... an) *)
        let@ (key_locals, _, _) = closure_context_sep Lambda Fresh naming_id loc in
        let* kpos = geti_term key_fixs pred_pos in
        let fix = mkApp (kpos, (Array.append inst_nuparams inst_indices)) in
        let* karg = get_term key_arg in
        let* kloc = get_terms key_locals in
        let arg = mkApp (karg, Array.of_list kloc) in
        return @@ mkApp (fix, [| arg |])
      )
    end
  | _ -> return None

(* Compute the arguments of the rec call *)
let compute_args_fix kn mdecl ind_bodies pos_list key_fixs key_args =
  CList.fold_right_i (fun pos_arg key_arg t ->
    let* karg = LibBinding.State.get_type key_arg in
    let* rec_call = make_rec_call kn mdecl ind_bodies key_fixs key_arg karg in
    let* karg' = get_term key_arg in
    let* t = t in
    match rec_call with
      | Some rc_tm -> let* rc_tm = rc_tm in
                return @@ karg' :: rc_tm :: t
      | None -> return @@ karg' :: t
  ) 0 key_args (return [])

let gen_elim print_constr env sigma kn u mdecl uparams nuparams (ind_bodies : elim_info list) (focus : int) =

  dbg Pp.(fun () -> str "\n------------------------------------------------------------- \n"
    ++ str (MutInd.to_string kn) ++ str " ## pos_ind : " ++ str (string_of_int focus) ++ str "\n") ;

  let t =

  (* 1. Closure Uparams / preds / ctors *)
  let@ (key_uparams, _, _) = closure_uparams Lambda naming_hd_fresh uparams in
  let@ key_preds = closure_preds kn u ind_bodies Lambda key_uparams nuparams in
  let@ key_ctors = closure_ctors kn mdecl u ind_bodies Lambda key_uparams nuparams key_preds in
  (* 2. Fixpoint *)
  let fix_name pos_list (_,_,_,sort) = make_annot (Name (Id.of_string "F")) (relevance_of_sort sort) in
  let fix_type pos_list _ = make_return_type  kn u ind_bodies pos_list key_uparams nuparams key_preds in
  let fix_rarg pos_list (_,ind,_,_) = (mdecl.mind_nparams - mdecl.mind_nparams_rec) + ind.mind_nrealargs in
  let is_rec = let (_, ind, _, _) = List.hd ind_bodies in
    List.length ind_bodies > 1 || Inductiveops.mis_is_recursive env ((kn, focus), mdecl, ind) in
  let@ (key_fixs, pos_list, (pos_ind, ind, dep, sort)) =
    (* Doe not create a fix if it is not-recursive and only has one inductive body *)
    if is_rec
    then make_fix ind_bodies focus fix_rarg fix_name fix_type
    else fun cc -> cc ([], 0, List.hd ind_bodies) in
  (* 3. Closure Nuparams / Indices / Var *)
  let@ (key_nuparams, _, _) = closure_nuparams Lambda naming_hd_fresh nuparams in
  let@ (key_indices , _, _) = closure_indices Lambda naming_hd_fresh ind u in
  let name_ind = make_annot Anonymous (ind_relevance ind u) in
  let* tind = make_ind ((kn, pos_ind), u) key_uparams key_nuparams key_indices in
  let@ key_VarMatch = make_binder Lambda naming_hd_fresh name_ind tind in
  let ccl =
  (* 4 Match to prove P ... x *)
    let* xup = get_terms key_uparams in
    let* xnup = get_terms key_nuparams in
    let params = Array.of_list (xup @ xnup) in
    let case_pred = make_ccl key_preds pos_list dep key_nuparams in
    let* xmatch = get_term key_VarMatch in
    let* xind = get_terms key_indices in
    let@ (key_args, _, _, pos_ctor) =
      make_case_or_projections naming_hd_fresh mdecl (kn, pos_ind) ind u key_uparams key_nuparams params
        xind case_pred (relevance_of_sort sort) (xmatch) in
    (* 5 Body of the branch *)
    let* hyp = getij_term key_ctors pos_list pos_ctor in
    let* cfix = compute_args_fix kn mdecl ind_bodies pos_list key_fixs key_args in
    let* xnup = get_terms key_nuparams in
    let args = xnup @ cfix in
    return @@ mkApp (hyp, Array.of_list args)
  in
  (* 6. If it is not-recursive, has primitive projections and is dependent => add a cast *)
  let* env = get_env in
  let projs = Environ.get_projections env (kn, pos_ind) in
  if is_rec || Option.is_empty projs || not dep then ccl else
  let* ty = make_ccl key_preds pos_list dep key_nuparams key_indices key_VarMatch in
  let* ccl = ccl in
  return @@ mkCast (ccl, DEFAULTcast, ty)

  in
  let t = t @@ State.make env sigma in
  dbg Pp.(fun () -> print_constr env sigma t ++ str "\n");
  t


(**********************************************************************)
(* build the eliminators mutual and individual *)

(* Check all dependent eliminations are allowed*)
let check_elim env sigma (kn, n) mib u lrecspec =
  List.iter (fun ((kni, ni),dep,s) ->
    (* Check that all the blocks can be eliminated to s *)
    let elim_allowed = Inductiveops.is_allowed_elimination sigma ((mib,mib.mind_packets.(ni)),u) s in
    if not elim_allowed
    then raise (RecursionSchemeError (env, NotAllowedCaseAnalysis (sigma, true, ESorts.kind sigma s, ((kn, ni), EInstance.kind sigma u))));
    (* Check if dep elim is allowed: rec (co)ind records with prim proj can not be eliminated dependently *)
    if dep && not (Inductiveops.has_dependent_elim (mib, mib.mind_packets.(ni)))
    then raise (RecursionSchemeError (env, NotAllowedDependentAnalysis (true, (kni, ni))));
  ) lrecspec

(* Check all the blocks are mutual, and not given twice *)
let check_mut env sigma (kn, n) mib u lrecspec =
  let _ : int list =
    List.fold_left (fun ln ((kni, ni),dep,s) ->
        (* Check all the blocks are mutual  *)
        if not (QMutInd.equal env kn kni)
        then raise (RecursionSchemeError (env, NotMutualInScheme ((kn, n),(kni, ni))));
        (* Check none is given twice *)
        if Int.List.mem ni ln
        then raise (RecursionSchemeError (env, DuplicateInductiveBlock (kn, ni)))
        else ni::ln)
      [n] lrecspec
  in
  ()

let build_mutual_induction_scheme env sigma ?(force_mutual=false) lrecspec u =
  match lrecspec with
  | (mind,dep,s)::tail ->
      let mib, mip = lookup_mind_specif env mind in
      (* Check the blocks are all mutual, different, and can be eliminated dependently *)
      let () = check_mut env sigma mind mib u tail in
      let () = check_elim env sigma mind mib u lrecspec in
      (* Compute values for gen_elim *)
      let listdepkind = (snd mind, mip, dep, s) :: List.map (fun ((_,ni), dep, s) -> (ni, mib.mind_packets.(ni), dep, s)) tail in
      (* Get parameters, and generalized them for UnivPoly + TemplatePoly *)
      let (sigma, uparams, nuparams) = get_params_sep sigma mib u in
      (* Compute eliminators *)
      let recs = List.init (List.length listdepkind) (gen_elim Termops.Internal.print_constr_env env sigma (fst mind) u mib uparams nuparams listdepkind) in
      (sigma, recs)
  | _ -> anomaly (Pp.str "build_mutual_induction_scheme expects a non empty list of inductive types.")

let build_induction_scheme env sigma (ind, u) dep kind =
  on_snd List.hd @@ build_mutual_induction_scheme env sigma [(ind, dep, kind)] u
