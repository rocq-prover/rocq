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
open Declarations
open Term
open Constr
open Context
open Vars
open Environ
open Inductive
open Vmvalues
open Vm
open Context.Rel.Declaration

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

(*******************************************)
(* Calcul de la forme normal d'un terme    *)
(*******************************************)

type context = {
  evars : CClosure.evar_handler;
  evar_type : Evar.t -> int * types;
  return_is_relevant : Environ.env -> Sorts.relevance -> bool;
}

let e_whd_all env ctx t = Reduction.whd_all ~evars:ctx.evars env t

let nf_all env ctx t =
  let infos = CClosure.create_clos_infos ~evars:ctx.evars RedFlags.all env in
  CClosure.norm_val infos (CClosure.create_tab ()) (CClosure.inject t)

let check_int63 env t = match kind t with
| Const (c, u) -> is_int63_type env c && UVars.Instance.is_empty u
| _ -> false

let crazy_type =  mkSet

let decompose_prod env sigma t =
  let (name,dom,codom) = destProd (e_whd_all env sigma t) in
  let name = map_annot (function
  | Anonymous -> Name (Id.of_string "x")
  | Name _ as na -> na) name
  in
  (name,dom,codom)

exception Find_at of int

(* rend le numero du constructeur correspondant au tag [tag],
   [cst] = true si c'est un constructeur constant *)

let invert_tag cst tag reloc_tbl =
  try
    for j = 0 to Array.length reloc_tbl - 1 do
      let tagj,arity = reloc_tbl.(j) in
      let no_arity = Int.equal arity 0 in
      if Int.equal tag tagj && (cst && no_arity || not (cst || no_arity)) then
        raise (Find_at j)
      else ()
    done;raise Not_found
  with Find_at j -> (j+1)
             (* Argggg, ces constructeurs de ... qui commencent a 1*)

let app_type env sigma c =
  let t = e_whd_all env sigma c in
  decompose_app t

let find_rectype_a env sigma c =
  let (t, l) = app_type env sigma c in
  match kind t with
  | Ind ind -> (ind, l)
  | _ -> raise Not_found

type env = {
  env : Environ.env;
  norm_params : bool;
}

let push_rel decl env =
  { env with env = Environ.push_rel decl env.env }

let push_rel_context ctx env =
  { env with env = Environ.push_rel_context ctx env.env }

let push_rels_assum ctx env =
  let fold (na, t) accu = Environ.push_rel (LocalAssum (na, t)) accu in
  { env with env = List.fold_right fold ctx env.env }

let push_rec_types rdef env =
  { env with env = Environ.push_rec_types rdef env.env }

let (!!) e = e.env

(* Instantiate inductives and parameters in constructor type *)

let type_constructor mib mip i u params =
  let (ctx, typ) = mip.mind_nf_lc.(i) in
  let ndecls = Context.Rel.length mib.mind_params_ctxt in
  if Int.equal ndecls 0 then
    (subst_instance_context u ctx, subst_instance_constr u typ)
  else
    let ctx = List.firstn mip.mind_consnrealdecls.(i) ctx in
    let ctyp = it_mkProd_or_LetIn typ ctx in
    let ctyp = subst_instance_constr u ctyp in
    let ctyp = substl (subst_of_rel_context_instance mib.mind_params_ctxt params) ctyp in
    Term.decompose_prod_decls ctyp

let construct_of_constr_block env sigma tag typ =
  let t, allargs = app_type !!env sigma typ in
  match Constr.kind t with
  | Ind (ind, u as indu) ->
    let mib,mip = lookup_mind_specif !!env ind in
    let nparams = mib.mind_nparams in
    let i = invert_tag false tag mip.mind_reloc_tbl in
    let params = if Int.equal mip.mind_nrealargs 0 then allargs else Array.sub allargs 0 nparams in
    let ctyp = type_constructor mib mip (i - 1) u params in
    let params =
      if env.norm_params then
        Array.map (nf_all !!env sigma) params
      else params
    in
    (mkApp(mkConstructUi(indu,i), params), ctyp)
  | _ ->
    let () = assert (check_int63 !!env t) in
    (mkInt (Uint63.of_int tag), ([], t))

let construct_of_constr_const env sigma tag typ =
  let t, allargs = app_type !!env sigma typ in
  match Constr.kind t with
  | Ind (ind, _ as indu) ->
    let mib,mip = lookup_mind_specif !!env ind in
    let nparams = mib.mind_nparams in
    let i = invert_tag true tag mip.mind_reloc_tbl in
    let params = if Int.equal mip.mind_nrealargs 0 then allargs else Array.sub allargs 0 nparams in
    let params =
      if env.norm_params then
        Array.map (nf_all !!env sigma) params
      else params
    in
    mkApp (mkConstructUi (indu, i), params)
  | _ ->
    assert (check_int63 !!env t);
    mkInt (Uint63.of_int tag)

let type_of_ind env (ind, u) =
  type_of_inductive (Inductive.lookup_mind_specif env ind, u)

let get_case_annot decls =
  Array.map_of_list (fun decl -> get_annot decl) (List.rev decls)

let build_branches_type env sigma mib mip u params (pctx, p) =
  let rtbl = mip.mind_reloc_tbl in
  (* [build_one_branch i cty] construit le type de la ieme branche (commence
     a 0) et les lambda correspondant aux realargs *)
  let p = it_mkLambda_or_LetIn p pctx in (* TODO: prevent useless cut? *)
  let build_one_branch i cty =
    let typi = type_constructor mib mip i u params in
    let typi = it_mkProd_or_LetIn (snd typi) (fst typi) in
    let decl,indapp = Reduction.whd_decompose_prod ~evars:sigma.evars env typi in
    let decl = List.map (fun d -> RelDecl.get_annot d, RelDecl.get_type d) decl in
    let ((ind,u),cargs) = find_rectype_a env sigma indapp in
    let nparams = Array.length params in
    let carity = snd (rtbl.(i)) in
    let crealargs = Array.sub cargs nparams (Array.length cargs - nparams) in
    let codom =
      let ndecl = List.length decl in
      let papp = mkApp(lift ndecl p,crealargs) in
      let cstr = ith_constructor_of_inductive ind (i+1) in
      let relargs = Array.init carity (fun i -> mkRel (carity-i)) in
      let params = Array.map (lift ndecl) params in
      let dep_cstr = mkApp(mkApp(mkConstructU (cstr,u),params),relargs) in
      mkApp(papp,[|dep_cstr|])
    in
    let decl_with_letin = List.firstn mip.mind_consnrealdecls.(i) (fst cty) in
    let nas = get_case_annot decl_with_letin in
    let nas = Array.map (Context.map_annot_relevance (UVars.subst_instance_relevance u)) nas in
    let rec get_lift decls = match decls with
    | [] -> Esubst.el_id
    | LocalDef _ :: decls -> Esubst.el_shft 1 (Esubst.el_lift (get_lift decls))
    | LocalAssum _ :: decls -> Esubst.el_lift (get_lift decls)
    in
    decl, nas, get_lift decl_with_letin, codom
  in Array.mapi build_one_branch mip.mind_nf_lc

let build_case_type (pctx, p) realargs c =
  let p = it_mkLambda_or_LetIn p pctx in (* TODO: prevent useless cut? *)
  mkApp(mkApp(p, realargs), [|c|])

(* La fonction de normalisation *)

let rec nf_val (env : env) sigma v t = nf_whd env sigma (Vmvalues.whd_val v) t

and nf_vtype env sigma v =  nf_val env sigma v crazy_type

and nf_whd env sigma whd typ =
  match whd with
  | Vprod p ->
      let dom = nf_vtype env sigma (dom p) in
      let name = Name (Id.of_string "x") in
      let vc = reduce_fun (nb_rel !!env) (codom p) in
      let r = Vmvalues.prod_relevance p in
      let name = make_annot name r in
      let codom = nf_vtype (push_rel (LocalAssum (name,dom)) env) sigma vc  in
      mkProd(name,dom,codom)
  | Vfun f -> nf_fun env sigma f typ
  | Vfix(f,None) -> nf_fix env sigma f
  | Vfix(f,Some vargs) -> fst (nf_fix_app env sigma f vargs)
  | Vcofix(cf,_,None) -> nf_cofix env sigma cf
  | Vcofix(cf,_,Some vargs) ->
      let cfd = nf_cofix env sigma cf in
      let i,(_,ta,_) = destCoFix cfd in
      let t = ta.(i) in
      let _, args = nf_args env sigma vargs t in
      mkApp(cfd,args)
  | Vconst n ->
    construct_of_constr_const env sigma n typ
  | Vblock b ->
      let tag = btag b in
      let (tag,ofs) =
        if tag = Obj.last_non_constant_constructor_tag then
          match whd_val (bfield b 0) with
          | Vconst tag -> (tag+Obj.last_non_constant_constructor_tag, 1)
          | _ -> assert false
        else (tag, 0) in
      let capp,ctyp = construct_of_constr_block env sigma tag typ in
      let args = nf_bargs env sigma b ofs ctyp in
      mkApp(capp,args)
  | Vint64 i -> i |> Uint63.of_int64 |> mkInt
  | Vfloat64 f -> f |> Float64.of_float |> mkFloat
  | Vstring s -> s |> mkString
  | Varray t -> nf_array env sigma t typ
  | Vaccu (Aid idkey, stk) ->
      constr_type_of_idkey env sigma idkey stk
  | Vaccu (Aind ((mi, _) as ind), stk) ->
     let mib = Environ.lookup_mind mi !!env in
     let nb_univs =
       UVars.AbstractContext.size (Declareops.inductive_polymorphic_context mib)
     in
     let mk u =
       let pind = (ind, u) in (mkIndU pind, type_of_ind !!env pind)
     in
     nf_univ_args ~nb_univs mk env sigma stk
  | Vaccu (Asort s, stk) ->
    assert (List.is_empty stk); mkSort s

and nf_univ_args ~nb_univs mk env sigma stk =
  let u =
    if UVars.eq_sizes nb_univs (0,0) then UVars.Instance.empty
    else match stk with
    | Zapp args :: _ ->
      let inst = arg args 0 in
      let inst = uni_instance inst in
      let () = assert (UVars.eq_sizes (UVars.Instance.length inst) nb_univs) in
      inst
    | _ -> assert false
  in
  let (t,ty) = mk u in
  let from = if UVars.Instance.is_empty u then 0 else 1 in
  nf_stk ~from env sigma t ty stk

and nf_evar env sigma evk stk =
  let n, typ = sigma.evar_type evk in
  if Int.equal n 0 then
    nf_stk env sigma (mkEvar (evk, SList.empty)) typ stk
  else match stk with
  | Zapp args :: stk ->
    let t, args = nf_args env sigma args typ in
    let inst, args = Array.chop n args in
    (* Evar instances are reversed w.r.t. argument order *)
    let inst = Array.to_list inst in
    let ev = sigma.evars.CClosure.evar_repack (evk, List.rev inst) in
    let c = mkApp (ev, args) in
    nf_stk env sigma c t stk
  | _ ->
    CErrors.anomaly (Pp.str "Argument size mismatch when decompiling an evar")

and constr_type_of_idkey env sigma (idkey : Vmvalues.id_key) stk =
  match idkey with
  | Vmvalues.ConstKey cst ->
     let cbody = CClosure.lookup_constant_handler !!env sigma.evars cst in
     let nb_univs =
       UVars.AbstractContext.size (Declareops.constant_polymorphic_context cbody)
     in
     let mk u =
       let ty = subst_instance_constr u cbody.const_type in
       (mkConstU (cst, u), ty)
     in
     nf_univ_args ~nb_univs mk env sigma stk
   | Vmvalues.VarKey id ->
      let ty = NamedDecl.get_type (lookup_named id !!env) in
      nf_stk env sigma (mkVar id) ty stk
  | Vmvalues.RelKey i ->
      let n = (nb_rel !!env - i) in
      let ty = RelDecl.get_type (lookup_rel n !!env) in
      nf_stk env sigma (mkRel n) (lift n ty) stk
  | EvarKey evk ->
      nf_evar env sigma evk stk

and nf_stk ?from:(from=0) env sigma c t stk  =
  match stk with
  | [] -> c
  | Zapp vargs :: stk ->
      if nargs vargs >= from then
        let t, args = nf_args ~from:from env sigma vargs t in
        nf_stk env sigma (mkApp(c,args)) t stk
      else
        let rest = from - nargs vargs in
        nf_stk ~from:rest env sigma c t stk
  | Zfix (f,vargs) :: stk ->
      assert (from = 0) ;
      let fa, typ = nf_fix_app env sigma f vargs in
      let _,_,codom = decompose_prod !!env sigma typ in
      nf_stk env sigma (mkApp(fa,[|c|])) (subst1 c codom) stk
  | Zswitch sw :: stk ->
      assert (from = 0) ;
      let (ind, u), allargs = find_rectype_a !!env sigma t in
      let (mib,mip) = Inductive.lookup_mind_specif !!env ind in
      let nparams = mib.mind_nparams in
      let params,realargs = Util.Array.chop nparams allargs in
      let pctx =
        let realdecls, _ = List.chop mip.mind_nrealdecls mip.mind_arity_ctxt in
        (* NB expand_arity doesn't look at the relevances in nas *)
        let nas = List.rev_map RelDecl.get_annot realdecls @ [nameR (Id.of_string "c")] in
        expand_arity (mib, mip) (ind, u) params (Array.of_list nas)
      in
      let pred = type_of_switch sw in
      let relevance = type_relevance pred in
      let p = nf_predicate env sigma (type_value pred) pctx in
      (* Calcul du type des branches *)
      let btypes = build_branches_type !!env sigma mib mip u params (pctx, p) in
      (* calcul des branches *)
      let bsw = branch_of_switch (nb_rel !!env) sw in
      let mkbranch i (_,v) =
        let decl, nas, lft, codom = btypes.(i) in
        let b = nf_val (push_rels_assum decl env) sigma v codom in
        (* No let-ins in [codom], so we have to ignore the ones from the branch *)
        let b = exliftn lft b in
        (nas, b)
      in
      let branchs = Array.mapi mkbranch bsw in
      let tcase = build_case_type (pctx, p) realargs c in
      let p = (get_case_annot pctx, p) in
      let ci = { ci_ind = ind; ci_npar = nparams;
        ci_cstr_ndecls = mip.mind_consnrealdecls;
        ci_cstr_nargs = mip.mind_consnrealargs; ci_pp_info = { style = MatchStyle } }
      in
      let return_is_relevant = sigma.return_is_relevant !!env relevance in
      let iv = if Inductive.should_invert_case !!env ~return_is_relevant ind then
          CaseInvert {indices=realargs}
        else NoInvert
      in
      nf_stk env sigma (mkCase (ci, u, params, (p,relevance), iv, c, branchs)) tcase stk
  | Zproj p :: stk ->
    let () = assert (from = 0) in
    let ((ind, u), args) = find_rectype_a !!env sigma t in
    let (mib, mip) = Inductive.lookup_mind_specif !!env ind in
    let pars = Array.sub args 0 mib.mind_nparams in
    let ty = match mip.mind_record with
    | NotRecord | FakeRecord -> assert false
    | PrimRecord { tys; _ } ->
      let ty = Vars.subst_instance_constr u tys.(p) in
      substl (c :: Array.fold_left (fun acc p -> p :: acc) [] pars) ty
    in
    let p, r = Declareops.inductive_make_projection ind mib ~proj_arg:p in
    let p = Projection.make p true in
    let r = UVars.subst_instance_relevance u r in
    nf_stk env sigma (mkProj (p, r, c)) ty stk

and nf_predicate env sigma v pctx =
  (* TODO: we should expose some variant of Vm.mkrel_vstack *)
  let fold decl (k, v) = match decl with
  | LocalDef _ -> (k + 1, v)
  | LocalAssum _ ->
    match whd_val v with
    | Vfun f -> (k + 1, reduce_fun k f)
    | _ -> assert false
  in
  let (_, v) = List.fold_right fold pctx (nb_rel !!env, v) in
  let env = push_rel_context pctx env in
  nf_vtype env sigma v

and nf_telescope env sigma len f typ =
  let open CClosure in
  let t = ref (inject typ) in
  let infos = CClosure.create_clos_infos ~evars:sigma.evars RedFlags.all !!env in
  let tab = create_tab () in
  let init i =
    let typ, stk = whd_stack infos tab !t [] in
    let typ = zip typ stk in
    match fterm_of typ with
    | FProd (_, dom, codom, e) ->
      let arg = f i in
      let dom = term_of_fconstr dom in
      let arg = nf_val env sigma arg dom in
      let () = t := mk_clos (CClosure.usubs_cons (inject arg) e) codom in
      arg
    | _ -> assert false
  in
  let args = Array.init len init in
  !t, args

and nf_args env sigma vargs ?from:(f=0) t =
  let len = nargs vargs - f in
  let fargs i = arg vargs (f + i) in
  let typ, args = nf_telescope env sigma len fargs t in
  CClosure.term_of_fconstr typ, args

and nf_bargs env sigma b ofs (ctx, _) =
  let rec norm i accu subst = function
  | [] -> accu
  | LocalAssum (_, dom) :: ctx ->
    let dom = Vars.esubst Vars.lift_substituend subst dom in
    let arg = nf_val env sigma (bfield b (i + ofs)) dom in
    let subst = Esubst.subs_cons (Vars.make_substituend arg) subst in
    norm (i + 1) (arg :: accu) subst ctx
  | LocalDef (_, def, _) :: ctx ->
    let def = Vars.esubst Vars.lift_substituend subst def in
    let subst = Esubst.subs_cons (Vars.make_substituend def) subst in
    norm i accu subst ctx
  in
  let ans = norm 0 [] (Esubst.subs_id 0) (List.rev ctx) in
  Array.rev_of_list ans

and nf_fun env sigma f typ =
  let k = nb_rel !!env in
  let vb = reduce_fun k f in
  let name,dom,codom = decompose_prod !!env sigma typ in
  let body = nf_val (push_rel (LocalAssum (name,dom)) env) sigma vb codom in
  mkLambda(name,dom,body)

and nf_fix env sigma f =
  let init = current_fix f in
  let rec_args = rec_args f in
  let k = nb_rel !!env in
  let vb, vt = reduce_fix k f in
  let ndef = Array.length vt in
  let ft = Array.map (fun t -> nf_vtype env sigma (type_value t)) vt in
  let name = Name (Id.of_string "Ffix") in
  let names = Array.map (fun t -> make_annot name (type_relevance t)) vt in
  (* Body argument of the tuple is ignored by push_rec_types *)
  let env = push_rec_types (names,ft,ft) env in
  (* We lift here because the types of arguments (in tt) will be evaluated
     in an environment where the fixpoints have been pushed *)
  let norm_vb v t = nf_fun env sigma v (lift ndef t) in
  let fb = Util.Array.map2 norm_vb vb ft in
  mkFix ((rec_args,init),(names,ft,fb))

and nf_fix_app env sigma f vargs =
  let fd = nf_fix env sigma f in
  let (_,i),(_,ta,_) = destFix fd in
  let t = ta.(i) in
  let t, args = nf_args env sigma vargs t in
  mkApp(fd,args),t

and nf_cofix env sigma cf =
  let init = current_cofix cf in
  let k = nb_rel !!env in
  let vb,vt = reduce_cofix k cf in
  let cft = Array.map (fun t -> nf_vtype env sigma (type_value t)) vt in
  let name = Name (Id.of_string "Fcofix") in
  let names = Array.map (fun t -> make_annot name (type_relevance t)) vt in
  let env = push_rec_types (names,cft,cft) env in
  let cfb = Util.Array.map2 (fun v t -> nf_val env sigma v t) vb cft in
  mkCoFix (init,(names,cft,cfb))

and nf_array env sigma t typ =
  let ty, allargs = app_type !!env sigma typ in
  let typ_elem = allargs.(0) in
  let vdef = Parray.default t in
  (* Do not cast into an array out of fear that floats may sneak in *)
  let init i = nf_val env sigma (Parray.get t (Uint63.of_int i)) typ_elem in
  let t = Array.init (Parray.length_int t) init in
  let u = snd (destConst ty) in
  mkArray(u, t, nf_val env sigma vdef typ_elem, typ_elem)

let readback ~normalize_params env ctx v typ =
  nf_val { env; norm_params = normalize_params } ctx v typ

let readback_type env ctx v =
  nf_vtype { env; norm_params = false } ctx v
