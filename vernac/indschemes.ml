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

(* This file provides entry points for manually or automatically
   declaring new schemes *)

open Pp
open Util
open Declarations
open Term
open Goptions
open Vernacexpr
open Ind_tables
open Auto_ind_decl
open Eqschemes
open Elimschemes

(** Data of an inductive scheme with name resolved *)
type resolved_scheme = Names.Id.t CAst.t * string list * Names.inductive * UnivGen.QualityOrSet.t option


(* Flags governing automatic synthesis of schemes *)

let elim_flag = ref true
let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Elimination";"Schemes"];
      optread  = (fun () -> !elim_flag) ;
      optwrite = (fun b -> elim_flag := b) }

let bifinite_elim_flag = ref false
let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Nonrecursive";"Elimination";"Schemes"];
      optread  = (fun () -> !bifinite_elim_flag) ;
      optwrite = (fun b -> bifinite_elim_flag := b) }

let case_flag = ref false
let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Case";"Analysis";"Schemes"];
      optread  = (fun () -> !case_flag) ;
      optwrite = (fun b -> case_flag := b) }

let eq_flag = ref false
let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Boolean";"Equality";"Schemes"];
      optread  = (fun () -> !eq_flag) ;
      optwrite = (fun b -> eq_flag := b) }

let is_eq_flag () = !eq_flag

let eq_dec_flag = ref false
let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Decidable";"Equality";"Schemes"];
      optread  = (fun () -> !eq_dec_flag) ;
      optwrite = (fun b -> eq_dec_flag := b) }

let rewriting_flag = ref false
let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Rewriting";"Schemes"];
      optread  = (fun () -> !rewriting_flag) ;
      optwrite = (fun b -> rewriting_flag := b) }

(* Util *)
let define ~poly ?loc name sigma c types =
  let poly =
    PolyFlags.of_univ_poly poly (* FIXME sortpoly and cumulative not supported *)
  in
  let univs = Evd.univ_entry ~poly sigma in
  let entry = Declare.definition_entry ~univs ?types c in
  let kind = Decls.(IsDefinition Scheme) in
  let kn = Declare.declare_constant ?loc ~kind ~name (Declare.DefinitionEntry entry) in
  Declare.definition_message name;
  kn

(* Boolean equality *)

let declare_beq_scheme_gen ?locmap names kn =
  ignore (define_mutual_scheme ?locmap beq_scheme_kind names kn)

let declare_beq_scheme_with ?locmap l kn =
  declare_beq_scheme_gen ?locmap l [kn,0]

open Auto_ind_decl

let debug = CDebug.create ~name:"indschemes" ()

let try_declare_beq_scheme ?locmap kn =
  (* TODO: handle Fix, eventually handle
      proof-irrelevance; improve decidability by depending on decidability
      for the parameters rather than on the bl and lb properties *)
  let mib = Global.lookup_mind kn in
  let n = Array.length mib.mind_packets in
  let rec mk_list l i =
    if i >= n then l
    else mk_list (List.append l [(kn,i)]) (i+1)
  in
  let l = mk_list [] 0 in
  try (define_mutual_scheme ?locmap beq_scheme_kind [] l)
  with CErrors.UserError e ->
    (debug Pp.(fun () ->
        hov 0 e ++ fnl () ++ str "Boolean Equality" ++ str " not defined."))

let declare_beq_scheme ?locmap mi = declare_beq_scheme_with ?locmap [] mi

(* Case analysis schemes *)
let declare_one_case_analysis_scheme ?loc ind =
  let (mib, mip) as specif = Global.lookup_inductive ind in
  let kind = Elimschemes.pseudo_sort_quality_for_elim ind mip in
  let dep, suff =
    if Sorts.Quality.is_qprop kind then case_nodep, Some "case"
    else if not (Inductiveops.has_dependent_elim specif) then
      case_nodep, None
    else case_dep, Some "case" in
  let id = match suff with
    | None -> None
    | Some suff ->
      (* the auto generated eliminator may be called "case" instead of eg "case_nodep" *)
      Some Names.(Id.of_string (Id.to_string mip.mind_typename ^ "_" ^ suff))
  in
  let kelim = Inductiveops.elim_sort (mib,mip) in
  if Inductive.raw_eliminates_to kelim Sorts.Quality.qtype then
    define_individual_scheme ?loc dep id ind

(* Induction/recursion schemes *)

let declare_one_induction_scheme ?loc ind =
  let (mib,mip) as specif = Global.lookup_inductive ind in
  let kind = Elimschemes.pseudo_sort_quality_for_elim ind mip in
  let from_prop = Sorts.Quality.is_qprop kind in
  let depelim = Inductiveops.has_dependent_elim specif in
  let kelim mip = Inductiveops.constant_sorts_below
              @@ Inductiveops.elim_sort (mib,mip) in
  let kelim =
    List.fold_right (fun x acc ->
      List.intersect UnivGen.QualityOrSet.equal acc x)
    (List.map kelim (Array.to_list mib.mind_packets))
    [UnivGen.QualityOrSet.qtype; UnivGen.QualityOrSet.prop; UnivGen.QualityOrSet.set; UnivGen.QualityOrSet.sprop] in
  let kelim =
    if Global.sprop_allowed ()
    then kelim
    else List.filter (fun s -> not (UnivGen.QualityOrSet.is_sprop s)) kelim
  in
  let elims =
    List.filter (fun (sort,_) -> List.mem_f UnivGen.QualityOrSet.equal sort kelim)
      [(UnivGen.QualityOrSet.qtype, "rect");
       (UnivGen.QualityOrSet.prop, "ind");
       (UnivGen.QualityOrSet.set, "rec");
       (UnivGen.QualityOrSet.sprop, "sind")]
  in
  let elims = List.map (fun (to_kind,dflt_suff) ->
      if from_prop then elim_scheme ~dep:false ~to_kind, Some dflt_suff
      else if depelim then elim_scheme ~dep:true ~to_kind, Some dflt_suff
      else elim_scheme ~dep:false ~to_kind, None)
      elims
  in
  List.iter (fun (kind, suff) ->
      let id = match suff with
        | None -> None
        | Some suff ->
          (* the auto generated eliminator may be called "rect" instead of eg "rect_dep" *)
          Some Names.(Id.of_string (Id.to_string mip.mind_typename ^ "_" ^ suff))
      in
      define_individual_scheme ?loc kind id ind)
         elims

let declare_induction_schemes ?(locmap=Locmap.default None) kn =
  let mib = Global.lookup_mind kn in
  if mib.mind_finite <> Declarations.CoFinite then begin
    for i = 0 to Array.length mib.mind_packets - 1 do
      let loc = Ind_tables.Locmap.lookup ~locmap (kn,i) in
      declare_one_induction_scheme (kn,i) ?loc;
    done;
  end

(* Decidable equality *)

let declare_eq_decidability_gen ?locmap names kn =
  let mib = Global.lookup_mind kn in
  if mib.mind_finite <> Declarations.CoFinite then
    define_mutual_scheme ?locmap eq_dec_scheme_kind names [(kn,0)]


let declare_eq_decidability_scheme_with ?locmap l kn =
  declare_eq_decidability_gen ?locmap l kn

let try_declare_eq_decidability ?locmap kn =
    let mib = Global.lookup_mind kn in
    if mib.mind_finite <> Declarations.CoFinite then
      try
        define_mutual_scheme ?locmap ~intern:true eq_dec_scheme_kind [] [kn,0]
      with  e when CErrors.noncritical e -> ()
  
let declare_eq_decidability ?locmap mi = declare_eq_decidability_scheme_with ?locmap [] mi

let ignore_error f x =
  try f x with e when CErrors.noncritical e -> ()

let declare_rewriting_schemes ?loc ind =
  if Hipattern.is_inductive_equality (Global.env ()) ind then begin
    (* Expect the equality to be symmetric *)
    ignore_error (define_individual_scheme ?loc sym_scheme_kind None) ind;
    define_individual_scheme ?loc rew_r2l_scheme_kind None ind;
    define_individual_scheme ?loc rew_r2l_dep_scheme_kind None ind;
    define_individual_scheme ?loc rew_r2l_forward_dep_scheme_kind None ind;
    (* These ones expect the equality to be symmetric; the first one also *)
    (* needs eq *)
    ignore_error (define_individual_scheme rew_l2r_scheme_kind None) ind;
    ignore_error
      (define_individual_scheme ?loc sym_involutive_scheme_kind None) ind;
    ignore_error
      (define_individual_scheme ?loc rew_l2r_dep_scheme_kind None) ind;
    ignore_error
      (define_individual_scheme ?loc rew_l2r_forward_dep_scheme_kind None) ind
  end

let warn_cannot_build_congruence =
  CWarnings.create ~name:"cannot-build-congruence" ~category:CWarnings.CoreCategories.automation
         (fun () ->
          strbrk "Cannot build congruence scheme because eq is not found")

let declare_congr_scheme ?loc ind =
  let env = Global.env () in
  if Hipattern.is_inductive_equality env ind then begin
    match Rocqlib.lib_ref_opt "core.eq.type" with
    | Some _ -> define_individual_scheme ?loc congr_scheme_kind None ind
    | None -> warn_cannot_build_congruence ()
  end

(* Scheme command *)

let smart_ind qid =
  let ind = Smartlocate.smart_global_inductive qid in
  if Dumpglob.dump() then Dumpglob.add_glob ?loc:qid.loc (IndRef ind);
  ind

(* Resolve the name of a scheme using an environment and extract some
   important data such as the inductive type involved, whether it is a dependent
   eliminator and its sort. *)
let name_and_process_scheme env = function
  | (Some id, {sch_type; sch_qualid; sch_sort}) ->
    (id, sch_type, smart_ind sch_qualid, sch_sort)
  | (None, {sch_type; sch_qualid; sch_sort}) ->
    let ind = smart_ind sch_qualid in
    let suffix =
      try Ind_tables.get_suff sch_type sch_sort
      with Not_found -> (fun _ -> "default")
    in
    let (mind,one_ind) = Global.lookup_inductive ind in
    let newid = Names.Id.of_string (suffix (Some one_ind)) in
    let newref = CAst.make newid in
    (newref,sch_type, ind, sch_sort)

let do_scheme ~register ?(force_mutual=false) env l =
  let l = List.map (name_and_process_scheme env) l in
  match l with
  (* if calling with one inductiv try define individual scheme *)
  | ({CAst.v},kind,(mutind,i as ind),sort)::[] ->
    (try
      define_individual_scheme (kind,sort,false) (Some v) ind
     with Not_found ->
      define_mutual_scheme (kind,sort,true) [(i,v)] [ind])
  | ({CAst.v},kind,(mutind,i),sort)::lrecspec ->
    let lnames = List.map (fun ({CAst.v},kind,(mutind,j),sort) -> (j,v)) l in
    let linds = List.map (fun ({CAst.v},kind,(mutind,j),sort) -> (mutind,j)) l in
    (try 
      define_mutual_scheme (kind,sort,true) lnames linds
    with Not_found -> CErrors.user_err Pp.(str "Mutually defined schemes should be recursive."))
  | _ -> (failwith "do_mutual_scheme expects a non empty list of inductive types.")

(* TODO : redifine do_mutual_induction_scheme using do_mutual_scheme *)
let do_mutual_induction_scheme ~register ?(force_mutual=false) env ?(isrec=true) l =
  let sigma = Evd.from_env env in
  let _,_,ind,_ = match l with | x::_ -> x | [] -> assert false in
  let sigma, (ind, inst) = Evd.fresh_inductive_instance env sigma ~rigid:UnivRigid ind in
  let sigma, lrecspec =
    List.fold_left_map (fun sigma (_,dep,ind,sort) ->
        let sigma, sort = Evd.fresh_sort_in_quality ~rigid:UnivRigid sigma sort in
        (sigma, (ind,dep,sort)))
      sigma
      l
  in
  let sigma, listdecl =
    if isrec then Indrec.build_mutual_induction_scheme env sigma ~force_mutual lrecspec inst
    else
      List.fold_left_map (fun sigma (ind,dep,sort) ->
          let sigma, c, _ = Indrec.build_case_analysis_scheme env sigma (ind, inst) dep sort in
          sigma, c)
        sigma lrecspec
  in
  let poly =
    (* NB: build_mutual_induction_scheme forces nonempty list of mutual inductives
       (force_mutual is about the generated schemes) *)
    let _,_,ind,_ = List.hd l in
    Global.is_polymorphic (Names.GlobRef.IndRef ind)
  in
  let is_mutual = isrec && List.length listdecl > 1 in
  let declare decl ({CAst.v=fi; loc},dep,ind, sort) =
    let decltype = Retyping.get_type_of env sigma decl in
    let decltype = EConstr.to_constr sigma decltype in
    let decl = EConstr.to_constr sigma decl in
    let cst = define ?loc ~poly fi sigma decl (Some decltype) in
    let kind =
      let open Elimschemes in
      let open UnivGen.QualityOrSet in
      if not register then None
      else if is_mutual then None (* don't make induction use mutual schemes *)
      else if isrec then Some (elim_scheme ~dep ~to_kind:sort)
      else match sort with
        | Qual (QConstant QType) -> Some (if dep then case_dep else case_nodep)
        | Qual (QConstant QProp) -> Some (if dep then casep_dep else casep_nodep)
        | Set | Qual (QConstant QSProp | QVar _) ->
          (* currently we don't have standard scheme kinds for this *)
          None
    in
    match kind with
    | None -> ()
    | Some kind ->
      (* TODO locality *)
      DeclareScheme.declare_scheme SuperGlobal kind (ind, Names.GlobRef.ConstRef cst)
  in
  let () = List.iter2 declare listdecl l in
  let lrecnames = List.map (fun ({CAst.v},_,_,_) -> v) l in
  Declare.fixpoint_message None lrecnames

let do_scheme_rewriting ?locmap id =
  let mind,_ as ind = smart_ind id in
  let loc = Option.bind locmap (fun locmap -> Locmap.lookup ~locmap ind) in
  declare_rewriting_schemes ?loc ind

(**********************************************************************)
(* Combined scheme *)
(* Matthieu Sozeau, Dec 2006 *)

let list_split_rev_at index l =
  let rec aux i acc = function
      hd :: tl when Int.equal i index -> acc, tl
    | hd :: tl -> aux (succ i) (hd :: acc) tl
    | [] -> failwith "List.split_when: Invalid argument"
  in aux 0 [] l

let fold_left' f = function
    [] -> invalid_arg "fold_left'"
  | hd :: tl -> List.fold_left f hd tl

let mk_rocq_and sigma = Evd.fresh_global (Global.env ()) sigma (Rocqlib.lib_ref "core.and.type")
let mk_rocq_conj sigma = Evd.fresh_global (Global.env ()) sigma (Rocqlib.lib_ref "core.and.conj")

let mk_rocq_prod sigma = Evd.fresh_global (Global.env ()) sigma (Rocqlib.lib_ref "core.prod.type")
let mk_rocq_pair sigma = Evd.fresh_global (Global.env ()) sigma (Rocqlib.lib_ref "core.prod.intro")

let build_combined_scheme env schemes =
  let sigma = Evd.from_env env in
  let sigma, defs = List.fold_left_map (fun sigma cst ->
    let sigma, c = Evd.fresh_constant_instance env sigma cst in
    let c = on_snd (EConstr.EInstance.kind sigma) c in
    sigma, (c, Typeops.type_of_constant_in env c)) sigma schemes in
  let find_inductive ty =
    let (ctx, arity) = decompose_prod ty in
    let (_, last) = List.hd ctx in
      match Constr.kind last with
        | Constr.App (ind, args) ->
            let ind = Constr.destInd ind in
            let (_,spec) = Inductive.lookup_mind_specif env (fst ind) in
              ctx, ind, spec.mind_nrealargs
        | _ -> ctx, Constr.destInd last, 0
  in
  let (c, t) = List.hd defs in
  let ctx, ind, nargs = find_inductive t in
  (* We check if ALL the predicates are in Prop, if so we use propositional
     conjunction '/\', otherwise we use the simple product '*'.
  *)
  let inprop =
    let inprop (_,t) =
      UnivGen.QualityOrSet.is_prop
        (Retyping.get_sort_quality_of env sigma (EConstr.of_constr t))
    in
    List.for_all inprop defs
  in
  let mk_and, mk_conj =
    if inprop
    then (mk_rocq_and, mk_rocq_conj)
    else (mk_rocq_prod, mk_rocq_pair)
  in
  (* Number of clauses, including the predicates quantification *)
  let prods = Termops.nb_prod sigma (EConstr.of_constr t) - (nargs + 1) in
  let sigma, rocqand  = mk_and sigma in
  let sigma, rocqconj = mk_conj sigma in
  let relargs = Termops.rel_vect 0 prods in
  let concls = List.rev_map
    (fun (cst, t) ->
      Constr.mkApp(Constr.mkConstU cst, relargs),
      snd (decompose_prod_n prods t)) defs in
  let concl_bod, concl_typ =
    fold_left'
      (fun (accb, acct) (cst, x) ->
        Constr.mkApp (EConstr.to_constr sigma rocqconj, [| x; acct; cst; accb |]),
        Constr.mkApp (EConstr.to_constr sigma rocqand, [| x; acct |])) concls
  in
  let ctx, _ =
    list_split_rev_at prods
      (List.rev_map (fun (x, y) -> Context.Rel.Declaration.LocalAssum (x, y)) ctx) in
  let typ = List.fold_left (fun d c -> Term.mkProd_wo_LetIn c d) concl_typ ctx in
  let body = it_mkLambda_or_LetIn concl_bod ctx in
  let sigma = Typing.check env sigma (EConstr.of_constr body) (EConstr.of_constr typ) in
  (sigma, body, typ)

let do_combined_scheme name csts =
  let open CAst in
  let sigma,body,typ = build_combined_scheme (Global.env ()) csts in
  (* It is possible for the constants to have different universe
     polymorphism from each other, however that is only when the user
     manually defined at least one of them (as Scheme would pick the
     polymorphism of the inductive block). In that case if they want
     some other polymorphism they can also manually define the
     combined scheme. *)
  let poly = Global.is_polymorphic (Names.GlobRef.ConstRef (List.hd csts)) in
  ignore (define ~poly ?loc:name.loc name.v sigma body (Some typ));
  Declare.fixpoint_message None [name.v]

(**********************************************************************)

let map_inductive_block ?(locmap=Locmap.default None) f kn n =
  for i=0 to n-1 do
    let loc = Ind_tables.Locmap.lookup ~locmap (kn,i) in
    f ?loc (kn,i)
  done

let declare_default_schemes ?locmap kn =
  let mib = Global.lookup_mind kn in
  let n = Array.length mib.mind_packets in
  if !elim_flag && (mib.mind_finite <> Declarations.BiFinite || !bifinite_elim_flag)
     && mib.mind_typing_flags.check_positive then
    declare_induction_schemes kn ?locmap;
  if !case_flag then map_inductive_block ?locmap declare_one_case_analysis_scheme kn n;
  if is_eq_flag() then try_declare_beq_scheme kn ?locmap;
  if !eq_dec_flag then try_declare_eq_decidability ?locmap kn;
  if !rewriting_flag then map_inductive_block ?locmap declare_congr_scheme kn n;
  if !rewriting_flag then map_inductive_block ?locmap declare_rewriting_schemes kn n
