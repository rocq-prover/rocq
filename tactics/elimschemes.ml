(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Hugo Herbelin from contents related to inductive schemes
   initially developed by Christine Paulin (induction schemes), Vincent
   Siles (decidable equality and boolean equality) and Matthieu Sozeau
   (combined scheme) in file command.ml, Sep 2009 *)

(* This file builds schemes related to case analysis and recursion schemes *)

open Names
open Indrec
open Declarations
open Ind_tables
open UnivGen

let prop_but_default_dependent_elim =
  Summary.ref ~name:"PROP-BUT-DEFAULT-DEPENDENT-ELIM" Indset_env.empty

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

let default_case_analysis_dependence env ind =
  let _, mip as specif = Inductive.lookup_mind_specif env ind in
  Inductiveops.has_dependent_elim specif
  && (not (Sorts.is_prop mip.mind_sort) || is_prop_but_default_dependent_elim ind)


(* **************************************************** *)
(*             Induction/recursion schemes              *)
(* **************************************************** *)

let build_induction_scheme_in_type env dep sort ind =
  let sigma = Evd.from_env env in
  let sigma, pind = Evd.fresh_inductive_instance ~rigid:UState.univ_rigid env sigma ind in
  let sigma, sort = Evd.fresh_sort_in_quality ~rigid:UnivRigid sigma sort in
  let sigma, c = build_induction_scheme env sigma pind dep sort in
  Some (EConstr.to_constr sigma c, Evd.ustate sigma)

let build_mutual_induction_scheme_in_type env dep sort isrec l =
  let ind,_ = match l with | x::_ -> x | [] -> assert false in
  let sigma, inst =
    let _, ctx = Typeops.type_of_global_in_context env (Names.GlobRef.IndRef (ind,0)) in
    let u, ctx = UnivGen.fresh_instance_from ctx None in
    let u = EConstr.EInstance.make u in
    let sigma = Evd.from_ctx (UState.of_context_set ctx) in
    sigma, u
  in
  let n = List.length l in
  let sigma, lrecspec =
    let rec loop i n sigma ll =
      if i>=n then (sigma,ll)
      else
        let new_sigma, new_sort = Evd.fresh_sort_in_quality ~rigid:UnivRigid sigma sort in
        let (indd,ii) = List.nth l i in
        let new_l = List.append ll [(((indd,ii),inst),dep,new_sort)] in
        loop (i + 1) n new_sigma new_l
    in
    loop 0 n sigma []
  in
  let sigma, listdecl =
    if isrec then Indrec.build_mutual_induction_scheme env sigma ~force_mutual:false lrecspec
    else
      List.fold_left_map (fun sigma (ind,dep,sort) ->
          let sigma, c = Indrec.build_case_analysis_scheme env sigma ind dep sort in
          let c, _ = Indrec.eval_case_analysis c in
          sigma, c)
        sigma lrecspec
  in
  let array = Array.of_list listdecl in
  let l = Array.map (fun x -> EConstr.to_constr sigma x) array in
  Some (l, Evd.ustate sigma)

let make_suff_sort one_ind suff dep =
  match one_ind with
  | None -> suff
  | Some i ->
    let sort = i.mind_sort
    in
    match sort with
    | Prop -> if dep then (Names.Id.to_string i.mind_typename) ^ "_" ^ suff ^ "_dep"
      else (Names.Id.to_string i.mind_typename) ^ "_" ^ suff
    | Type _ | SProp | Set -> if dep then (Names.Id.to_string i.mind_typename) ^ "_" ^ suff
      else (Names.Id.to_string i.mind_typename) ^ "_" ^ suff ^ "_nodep"
    | QSort _ -> (Names.Id.to_string i.mind_typename) ^ "_" ^ suff

let rect_dep =
  declare_individual_scheme_object (["Induction"], Some QualityOrSet.qtype)
    (fun id -> make_suff_sort id "rect" true)
    (fun env _ x _ -> build_induction_scheme_in_type env true QualityOrSet.qtype x)

let mutual_rect_dep =
  declare_mutual_scheme_object (["Induction"], Some QualityOrSet.qtype)
    (fun id -> make_suff_sort id "rect" true)
    (fun env _ x _ -> build_mutual_induction_scheme_in_type env true QualityOrSet.qtype true x)

let rec_dep =
  declare_individual_scheme_object (["Induction"], Some QualityOrSet.set)
    (fun id -> make_suff_sort id "rec" true)
    (fun env _ x _ -> build_induction_scheme_in_type env true QualityOrSet.set x)

let mutual_rec_dep =
  declare_mutual_scheme_object (["Induction"], Some QualityOrSet.set)
    (fun id -> make_suff_sort id "rec" true)
    (fun env _ x _ -> build_mutual_induction_scheme_in_type env true QualityOrSet.set true x)

let ind_dep =
  declare_individual_scheme_object (["Induction"], Some QualityOrSet.prop)
    (fun id -> make_suff_sort id "ind" true)
    (fun env _ x _ -> build_induction_scheme_in_type env true QualityOrSet.prop x)

let mutual_ind_dep =
  declare_mutual_scheme_object (["Induction"], Some QualityOrSet.prop)
    (fun id -> make_suff_sort id "ind" true)
    (fun env _ x _ -> build_mutual_induction_scheme_in_type env true QualityOrSet.prop true x)

let sind_dep =
  declare_individual_scheme_object (["Induction"], Some QualityOrSet.sprop)
    (fun id -> make_suff_sort id "inds" true)
    (fun env _ x _ -> build_induction_scheme_in_type env true QualityOrSet.sprop x)

let mutual_sind_dep =
  declare_mutual_scheme_object (["Induction"], Some QualityOrSet.sprop)
    (fun id -> make_suff_sort id "inds" true)
    (fun env _ x _ -> build_mutual_induction_scheme_in_type env true QualityOrSet.sprop true x)

let rect_nodep =
  declare_individual_scheme_object (["Minimality"], Some QualityOrSet.qtype)
    (fun id -> make_suff_sort id "rect" false)
    (fun env _ x _ -> build_induction_scheme_in_type env false QualityOrSet.qtype x)

let mutual_rect_nodep =
  declare_mutual_scheme_object (["Minimality"], Some QualityOrSet.qtype)
    (fun id -> make_suff_sort id "rect" false)
    (fun env _ x _ -> build_mutual_induction_scheme_in_type env false QualityOrSet.qtype true x)

let rec_nodep =
  declare_individual_scheme_object (["Minimality"], Some QualityOrSet.set)
    (fun id -> make_suff_sort id "rec" false)
    (fun env _ x _ -> build_induction_scheme_in_type env false QualityOrSet.set x)

let mutual_rec_nodep =
  declare_mutual_scheme_object (["Minimality"], Some QualityOrSet.set)
    (fun id -> make_suff_sort id "rec" false)
    (fun env _ x _ -> build_mutual_induction_scheme_in_type env false QualityOrSet.set true x)

let ind_nodep =
  declare_individual_scheme_object (["Minimality"], Some QualityOrSet.prop)
    (fun id -> make_suff_sort id "ind" false)
    (fun env _ x _ -> build_induction_scheme_in_type env false QualityOrSet.prop x)

let mutual_ind_nodep =
  declare_mutual_scheme_object (["Minimality"], Some QualityOrSet.prop)
    (fun id -> make_suff_sort id "ind" false)
    (fun env _ x _ -> build_mutual_induction_scheme_in_type env false QualityOrSet.prop true x)

let sind_nodep =
  declare_individual_scheme_object (["Minimality"], Some QualityOrSet.sprop)
    (fun id -> make_suff_sort id "inds" false)
    (fun env _ x _ -> build_induction_scheme_in_type env false QualityOrSet.sprop x)

let mutual_sind_nodep =
  declare_mutual_scheme_object (["Minimality"], Some QualityOrSet.sprop)
    (fun id -> make_suff_sort id "inds" false)
    (fun env _ x _ -> build_mutual_induction_scheme_in_type env false QualityOrSet.sprop true x)

let elim_scheme ~dep ~to_kind =
  let open QualityOrSet in
  match to_kind with
  | Qual q ->
     begin
       match q with
       | QConstant QSProp when dep -> sind_dep
       | QConstant QProp when dep -> ind_dep
       | (QConstant QType | QVar _) when dep -> rect_dep
       | QConstant QSProp -> sind_nodep
       | QConstant QProp -> ind_nodep
       | QConstant QType | QVar _ -> rect_nodep
     end
  | Set -> if dep then rec_dep else rec_nodep

let elimination_suffix =
  let open UnivGen.QualityOrSet in
  let open Sorts.Quality in
  function
  | Qual (QConstant QSProp) -> "_sind"
  | Qual (QConstant QProp) -> "_ind"
  | Qual (QConstant QType) | Qual (QVar _) -> "_rect"
  | Set -> "_rec"

let make_elimination_ident id s = Nameops.add_suffix id (elimination_suffix s)

(* Look up function for the default elimination constant *)

let lookup_eliminator_by_name env ind_sp s =
  let open Names in
  let open Environ in
  let kn,i = ind_sp in
  let mpu = KerName.modpath @@ MutInd.user kn in
  let mpc = KerName.modpath @@ MutInd.canonical kn in
  let ind_id = (lookup_mind kn env).mind_packets.(i).mind_typename in
  let id = make_elimination_ident ind_id s in
  let knu = KerName.make mpu id in
  let knc = KerName.make mpc id in
  (* Try first to get an eliminator defined in the same section as the *)
  (* inductive type *)
  let cst = Constant.make knu knc in
  if mem_constant cst env then GlobRef.ConstRef cst
  else
    (* Then try to get a user-defined eliminator in some other places *)
    (* using short name (e.g. for "eq_rec") *)
    try Nametab.locate (Libnames.qualid_of_ident id)
    with Not_found ->
      CErrors.user_err
        Pp.(strbrk "Cannot find the elimination combinator " ++
            Id.print id ++ strbrk ", the elimination of the inductive definition " ++
            Nametab.pr_global_env Id.Set.empty (GlobRef.IndRef ind_sp) ++
            strbrk " on sort " ++ UnivGen.QualityOrSet.pr Sorts.QVar.raw_pr s ++
            strbrk " is probably not allowed.")

let deprecated_lookup_by_name =
  CWarnings.create ~name:"deprecated-lookup-elim-by-name" ~category:Deprecation.Version.v9_1
    Pp.(fun (env,ind,to_kind,r) ->
        let pp_scheme () s = str (match scheme_kind_name s with (ss,_,_) -> String.concat " " ss) in
        fmt "Found unregistered eliminator %t for %t by name.@ \
             Use \"Register Scheme\" with it instead@ \
             (\"as %a\" if dependent or \"as %a\" if non dependent)."
          (fun () -> Termops.pr_global_env env r)
          (fun () -> Termops.pr_global_env env (IndRef ind))
          pp_scheme (elim_scheme ~dep:true ~to_kind)
          pp_scheme (elim_scheme ~dep:false ~to_kind))

let lookup_eliminator_by_name env ind s =
  let r = lookup_eliminator_by_name env ind s in
  deprecated_lookup_by_name (env,ind,s,r);
  r

let lookup_eliminator env ind s =
  let nodep_scheme_first =
    (* compat, add an option to control this and remove someday *)
    let _, mip = Inductive.lookup_mind_specif env ind in
    Sorts.is_prop mip.mind_sort && not (is_prop_but_default_dependent_elim ind)
  in
  let schemes =
    List.map (fun dep -> elim_scheme ~dep ~to_kind:s)
      (if nodep_scheme_first then [false;true] else [true;false])
  in
  match List.find_map (fun scheme -> lookup_scheme scheme ind) schemes with
  | Some c -> c
  | None ->
    (* XXX also lookup_scheme at less precise sort? eg if s=set try to_kind:qtype *)
    lookup_eliminator_by_name env ind s


(* **************************************************** *)
(*                    Case Analysis                     *)
(* **************************************************** *)

let build_case_analysis_scheme_in_type env dep sort ind =
  let sigma = Evd.from_env env in
  let (sigma, indu) = Evd.fresh_inductive_instance env sigma ind in
  let sigma, sort = Evd.fresh_sort_in_quality ~rigid:UnivRigid sigma sort in
  let (sigma, c, _) = build_case_analysis_scheme env sigma indu dep sort in
  Some (EConstr.Unsafe.to_constr c, Evd.ustate sigma)

let case_dep =
    declare_individual_scheme_object (["Elimination"], Some QualityOrSet.qtype)
      (fun id -> make_suff_sort id "caset" true)
      (fun env _ x _ -> build_case_analysis_scheme_in_type env true QualityOrSet.qtype x)

let casep_dep =
    declare_individual_scheme_object (["Elimination"], Some QualityOrSet.prop)
      (fun id -> make_suff_sort id "case" true)
      (fun env _ x _ -> build_case_analysis_scheme_in_type env true QualityOrSet.prop x)

let cases_dep =
    declare_individual_scheme_object (["Elimination"], Some QualityOrSet.sprop)
      (fun id -> make_suff_sort id "cases" true)
      (fun env _ x _ -> build_case_analysis_scheme_in_type env true QualityOrSet.sprop x)

let casep_dep_set =
    declare_individual_scheme_object (["Elimination"], Some QualityOrSet.set)
      (fun id -> make_suff_sort id "case" true)
      (fun env _ x _ -> build_case_analysis_scheme_in_type env true QualityOrSet.set x)

let case_nodep =
    declare_individual_scheme_object (["Case"], Some QualityOrSet.qtype)
      (fun id -> make_suff_sort id "caset" false)
      (fun env _ x _ -> build_case_analysis_scheme_in_type env false QualityOrSet.qtype x)

let casep_nodep =
    declare_individual_scheme_object (["Case"], Some QualityOrSet.prop)
      (fun id -> make_suff_sort id "case" false)
      (fun env _ x _ -> build_case_analysis_scheme_in_type env false QualityOrSet.prop x)

let cases_nodep =
    declare_individual_scheme_object (["Case"], Some QualityOrSet.sprop)
      (fun id -> make_suff_sort id "cases" false)
      (fun env _ x _ -> build_case_analysis_scheme_in_type env false QualityOrSet.sprop x)

let case_nodep_set =
    declare_individual_scheme_object (["Case"], Some QualityOrSet.set)
      (fun id -> make_suff_sort id "case" false)
      (fun env _ x _ -> build_case_analysis_scheme_in_type env false QualityOrSet.set x)      
