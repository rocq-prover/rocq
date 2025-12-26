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
open Constr
open EConstr
open Declarations
open Context
open Inductive
open Environ
open LibBinding
open State
open Retyping
open Rel.Declaration

let rec pp_list f l = match l with
  | []   -> Pp.str "]"
  | [a]  -> f a ++ Pp.str "]"
  | a::l -> f a ++ str "; " ++ pp_list f l

let pp_lint l = Pp.str "[" ++ pp_list Pp.int l
let pp_lbool l = Pp.str "[" ++ pp_list Pp.bool l

let (let@) x f = x f
let (let*) x f = State.bind x f
let dbg = CDebug.create ~name:"sparse_parametricity" ()

let print_term s t =
  let* env = get_env in
  let* sigma = get_sigma in
  return @@ dbg Pp.(fun () -> str s ++ Termops.Internal.print_constr_env env sigma t)

let print_context s =
  let* env = get_env in
  let* sigma = get_sigma in
  return @@ dbg Pp.(fun () -> str s ++ Termops.Internal.print_rel_context env sigma)

let print_str s =
  dbg Pp.(fun () -> str s)

  (** {6 Lookup Sparse Parametricity } *)

let warn_no_sparse_parametricity =
  CWarnings.create ~name:"no-All" ~category:Deprecation.Version.v9_2
  Pp.(fun (ind, ind_nested) ->
    Nametab.XRefs.pr (TrueGlobal (IndRef ind)) ++ str " is nested using " ++  Nametab.XRefs.pr (TrueGlobal (IndRef ind_nested)) ++
    str " but no all predicate for " ++ Nametab.XRefs.pr (TrueGlobal (IndRef ind_nested)) ++ str " is registered.\n"
    )

let warn_no_local_fundamental_theorem =
  CWarnings.create ~name:"no-All_Forall" ~category:Deprecation.Version.v9_2
  Pp.(fun (ind,ind_nested) ->
    Nametab.XRefs.pr (TrueGlobal (IndRef ind)) ++ str " is nested using " ++  Nametab.XRefs.pr (TrueGlobal (IndRef ind_nested)) ++
    str " but no lemma Forall lemma for " ++ Nametab.XRefs.pr (TrueGlobal (IndRef ind_nested)) ++ str " is registered.\n"
    )

let lookup_sparse_parametricity_only ind ind_nested =
    match Ind_tables.lookup_scheme "All" ind_nested with
    | None -> warn_no_sparse_parametricity (ind, ind_nested); None
    | Some ref_sparam -> Some ref_sparam

let lookup_sparse_parametricity ind ind_nested =
    match Ind_tables.lookup_scheme "All" ind_nested with
    | None -> warn_no_sparse_parametricity (ind, ind_nested); None
    | Some ref_sparam ->
    match Ind_tables.lookup_scheme "AllForall" ind_nested with
    | None -> warn_no_local_fundamental_theorem (ind, ind_nested); None
    | Some ref_lfth -> Some (ref_sparam, ref_lfth)


  (** {6 Instantiate Sparse Parametricity } *)

let mkFunUnit x =
  let@ _ = rebind fid Lambda Fresh naming_id x in
  return @@ mkRef ((Rocqlib.lib_ref "core.unit.type"), EInstance.empty)

let instantiate_sparse_parametricity inst_uparams strpos preds =
  let preds = Array.to_list preds in
  let inst_uparams = Array.to_list inst_uparams in
  let* s = get_state in
  let inst_sparam =
    List.fold_right (fun (inst_uparam, b, pred) acc ->
      if not b then inst_uparam :: acc else
      match pred with
      | None -> inst_uparam :: (snd @@ mkFunUnit inst_uparam s) :: acc
      | Some pred -> inst_uparam :: pred :: acc
      )
    (List.combine3 inst_uparams strpos preds) []
  in
  return @@ Array.of_list inst_sparam

let mkFuntt x =
  let@ _ = rebind fid Lambda Fresh naming_id x in
  return @@ mkRef ((Rocqlib.lib_ref "core.unit.tt"), EInstance.empty)

let instantiate_fundamental_theorem inst_uparams strpos preds preds_hold =
  let inst_uparams = Array.to_list inst_uparams in
  let preds = Array.to_list preds in
  let preds_hold = Array.to_list preds_hold in
  let* s = get_state in
  let inst_lfth =
    List.fold_right (fun (inst_uparam, b, (pred, pred_hold)) acc ->
      if not b then inst_uparam :: acc else
      match pred, pred_hold with
      | None, None -> inst_uparam :: (snd @@ mkFunUnit inst_uparam s) :: (snd @@ mkFuntt inst_uparam s) :: acc
      | Some pred, Some pred_hold -> inst_uparam :: pred :: pred_hold :: acc
      | _, _ -> assert false
    )
    (List.combine3 inst_uparams strpos @@ List.combine preds preds_hold) []
  in
  return @@ Array.of_list inst_lfth


  (** {6 View for Arguments } *)

 let find_opt_i p l =
    let rec aux i l = match l with
    | [] -> None
    | h::_ when p i h -> Some (i, h)
    | _::t -> aux (1+i) t
    in aux 0 l

type head_arg =
  | ArgIsSPUparam of int * constr array
  (** constant context, position of the uniform parameter, args *)
  | ArgIsInd of int * constr array * constr array
  (** constant context, position of the one_inductive body, inst_nuparams inst_indices *)
  | ArgIsNested of MutInd.t * int * mutual_inductive_body * bool list
                    * one_inductive_body * constr array * constr array
  (** constant context, ind_nested, mutual and one body, strictly positivity of its uniform parameters,
      instantiation uniform paramerters, and of both non_uniform parameters and indices *)
  | ArgIsCst

(** View to decompose arguments as [forall locs, X] where [X] is further decomposed
    as a uniform parameter, the inductive, a nested argument or a constant. *)
type arg = rel_context * head_arg

let check_key_in k keys =
  let* k = make_key k in
  return @@ Option.map fst @@ find_opt_i (fun _ key -> k = key) keys

(* Decompose the argument in [it_Prod_or_LetIn local, X] where [X] is a uniform parameter, Ind, nested or a constant *)
let view_arg kn mib key_uparams strpos t : arg State.t =
  let* (cxt, hd) = whd_decompose_prod_decls t in
  let* (hd, iargs) = decompose_app hd in
  let* sigma = get_sigma in
  match kind sigma hd with
  | Rel k -> begin
      (* Check if the debruijn variable corresponds to a strictly positive uniform parameter *)
      let* pos_up = check_key_in k key_uparams in
      match pos_up with
      | None   -> return @@ (cxt, ArgIsCst)
      | Some i -> if List.nth strpos i
                  then return @@ (cxt, ArgIsSPUparam (i, iargs))
                  else return @@ (cxt, ArgIsCst)
    end
  | Ind ((kn_ind, pos_ind), _) ->
    (* If it is the inductive *)
    if kn = kn_ind
    then let (_, local_nuparams_indices) = Array.chop mib.mind_nparams_rec iargs in
         let nb_nuparams = mib.mind_nparams - mib.mind_nparams_rec in
         let (local_nuparams, local_indices) = Array.chop nb_nuparams local_nuparams_indices in
         return @@ (cxt, ArgIsInd (pos_ind, local_nuparams, local_indices))
    (* if there is no argument, it cannot be nested *)
    else if Array.length iargs = 0 then return @@ (cxt, ArgIsCst)
    else begin
      (* If it may be nested *)
      let* env = get_env in
      let (mib_nested, ind_nested) = lookup_mind_specif env (kn_ind, pos_ind) in
      let mib_nested_strpos = Positive_parameters.compute_params_rec_strpos env kn_ind mib_nested in
      (* Check if at least one parameter can be nested upon *)
      if List.exists (fun a -> a) mib_nested_strpos then
        let (inst_uparams, inst_nuparams_indices) = Array.chop mib_nested.mind_nparams_rec iargs in
        return @@ (cxt, ArgIsNested (kn_ind, pos_ind, mib_nested, mib_nested_strpos,
                                ind_nested, inst_uparams, inst_nuparams_indices))
      else return @@ (cxt, ArgIsCst)
    end
  | _ -> return @@ (cxt, ArgIsCst)

  (** {6 Generate Sparse Parametricity } *)

(* To build sparse parametricity:
- For each positive uniform parameter [A : Type] add a predicate [PA : A -> Type]
- For each argument [a : A] add [PA a], for each inductive a recursion hypothesis
- Replace [tInd] by the corresponding [rel]
*)

  (** {7 Functions on Parameters } *)

let paramdecls_fresh_template sigma (mib,u) =
  match mib.mind_template with
  | None ->
    let params = Inductive.inductive_paramdecls (mib, EConstr.Unsafe.to_instance u) in
    sigma, EConstr.of_rel_context params, None
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
    let csts, params, sub = Inductive.instantiate_template_universes mib univs in
    let sigma = Evd.add_poly_constraints QGraph.Internal sigma csts in
    (sigma, EConstr.of_rel_context params, Some sub)

(** Generalize parameters for template and univ poly, and split uniform and non-uniform parameters *)
let get_params_sep sigma mib u =
  let (sigma, up_params, sub_temp) = paramdecls_fresh_template sigma (mib, u) in
  let (uparams, nuparams) = Declareops.split_uparans_nuparams mib.mind_nparams_rec up_params in
  (sigma, uparams, nuparams, sub_temp)

(** Closure of non-uniform parameters if [b], forgetting letins  *)
let closure_nuparams m binder naming_scheme nuparams =
  closure_context m binder Old naming_scheme nuparams

let add_context_nuparams naming_scheme nuparams =
  add_context Old naming_scheme nuparams

(** Compute relevance of an inductive block *)
let ind_relevance ind u =
  let* sigma = get_sigma in
  return @@ ERelevance.make @@ relevance_of_ind_body ind (EInstance.kind sigma u)

(** Closure for indices. They are considered as [Fresh] as they are not in the context of the arguments *)
let closure_indices m binder freshness naming_scheme indb u f =
  let* i = get_indices indb u in
  closure_context m binder freshness naming_scheme i f


    (** {7 Generate the Type of the Sparse Parametricity } *)

(** Given a positive uniform parameters, return its position among positive ones *)
let up_to_spup j strpos =
  let rec aux i n l =
    match l with
    | [] -> assert false
    | x::_ when x && i = j -> n
    | x::l when x -> aux (i+1) (n+1) l
    | _ :: l -> aux (i+1) n l
  in
  aux 0 0 strpos

(** Create a fresh predicate *)
let mkPred key_arg s =
  let* arg_ty = State.get_type key_arg in
  let* (locs, hd) = whd_decompose_prod_decls arg_ty in
  let@ key_locs = closure_context fid Prod Fresh naming_hd locs in
  (* make args *)
  let* loc = get_terms key_locs in
  let* arg_tm = get_term key_arg in
  let arg = mkApp (arg_tm, loc) in
  (* rev *)
  let* sigma = get_sigma in
  let sort = destSort sigma hd in
  let arg_rev = ESorts.relevance_of_sort sort in
  let name_hd = make_annot Anonymous arg_rev in
  (* bind *)
  let@ key_hd = build_binder fid Prod Fresh naming_id @@ LocalAssum (name_hd, arg) in
  return s

(** Take the closure of the uniform parameters adding fresh predicates for
    strictly positive uniform parameters [PA : A -> Type] *)
let closure_uparams_preds_gen binder uparams strpos fresh_sorts cc =
  let rec aux i key_uparams key_preds key_both tel cc =
    match tel with
    | [] -> cc ((List.rev key_uparams), (List.rev key_preds), (List.rev key_both))
    | decl :: tel ->
        let@ key_up = binder Old naming_id decl in
        if (Option.has_some @@ get_value decl) then
          aux i key_uparams key_preds key_both tel cc
        else if not (List.nth strpos i) then
          aux (i+1) (key_up::key_uparams) key_preds (key_up::key_both) tel cc
        else
          (* create (PA : A -> s) *)
          let name = Name.map_id (fun id -> Id.of_string @@ "P" ^ Id.to_string id) (get_name decl) in
          let name_pred = make_annot name ERelevance.relevant in
          let pred_sort_info = List.nth fresh_sorts @@ up_to_spup i strpos in
          let* type_pred = mkPred key_up @@ mkSort @@ ESorts.make @@ (fun (a,b) -> Sorts.qsort a b) pred_sort_info in
          let@ key_pred = binder Fresh naming_id @@ LocalAssum (name_pred, type_pred) in
          aux (i+1) (key_up::key_uparams) (key_pred::key_preds) (key_pred::key_up::key_both) tel cc
  in
  aux 0 [] [] [] (List.rev uparams) cc

let closure_uparams_preds binder uparams strpos fresh_sorts cc =
  closure_uparams_preds_gen (build_binder fid binder) uparams strpos fresh_sorts cc

let context_uparams_preds uparams strpos fresh_sorts =
  closure_uparams_preds_gen add_decl uparams strpos fresh_sorts

    (** {7 Compute Return Sort}  *)


(* Compute if an inductive is nested including for positive parameters to
   be able to create a fresh universe to handle the lack of algebraic universes *)
let rec is_nested_arg_nested kn mib key_uparams strpos arg : bool t =
  let* (locs, hd) = view_arg kn mib key_uparams strpos arg in
  let@ _ = add_context Old naming_id locs in
  match hd with
  | ArgIsNested (_, _, mib_nested, _, _, inst_uparams, _) ->
      let uparams_nested = of_rel_context @@ fst @@
            Declareops.split_uparans_nuparams mib_nested.mind_nparams_rec mib_nested.mind_params_ctxt in
      let* inst_uparams = eta_expand_instantiation inst_uparams uparams_nested in
      let* inst_uparams = array_mapi (fun _ arg ->
            let* (loc, hd) = decompose_lambda_decls arg in
            let@ _ = add_context Old naming_id loc in
            return hd
            ) inst_uparams
      in
      let* inst_uparams = array_mapi (fun _ -> is_nested_arg_nested kn mib key_uparams strpos) inst_uparams in
      return @@ Array.exists (fun x -> x) inst_uparams
  | ArgIsSPUparam  _ | ArgIsInd _ -> return true
  | _ -> return false

let is_nested_arg kn mib key_uparams strpos arg =
  let* (locs, hd) = view_arg kn mib key_uparams strpos arg in
  let@ _ = add_context Old naming_id locs in
  match hd with
  | ArgIsNested (_, _, mib_nested, _, _, inst_uparams, _) ->
      let uparams_nested = of_rel_context @@ fst @@
            Declareops.split_uparans_nuparams mib_nested.mind_nparams_rec mib_nested.mind_params_ctxt in
      let* inst_uparams = eta_expand_instantiation inst_uparams uparams_nested in
      let* inst_uparams = array_mapi (fun _ arg ->
            let* (loc, hd) = decompose_lambda_decls arg in
            let@ _ = add_context Old naming_id loc in
            return hd
            ) inst_uparams
      in
      let* inst_uparams = array_mapi (fun _ -> is_nested_arg_nested kn mib key_uparams strpos) inst_uparams in
      return @@ Array.exists (fun x -> x) inst_uparams
  | _ -> return false

let is_nested_ind kn mib ind uparams nuparams strpos : bool t =
  let@ key_uparams = add_context Old naming_id uparams in
  let@ _ = add_context Old naming_id nuparams in
  let* s = get_state in
  return @@
  Array.exists (fun ctor -> snd @@
      (let* (args, indices) = get_args mib EInstance.empty ctor in
      fold_left_state (fun a l -> a::l) args (
          fun _ arg cc ->
          let* arg_is_nested = is_nested_arg kn mib key_uparams strpos (get_type arg) in
          let@ key_arg  = add_decl Old naming_id arg in
          let* b = cc key_arg in
          return (arg_is_nested || b)
        ) (fun _ -> return false) ) s
    ) ind.mind_nf_lc

let sup_list us u =
  List.fold_right Univ.Universe.sup us u

(** Compute the return sort of sparse parametricity adding to original type
    the sorts level of the predicates, and if nested a new universe level to accumulates
    constrains coming from the instantation of the sparse parametricity of nested arguments
    which would require algebraic universes otherwise *)
let compute_one_return_sort mib ind is_nested u sub_temp fresh_sorts =
  let open Sorts in
  (* Return the sort of the inductive *)
  let u = Evd.MiniEConstr.EInstance.unsafe_to_instance u in
  let ind_sort = UVars.subst_instance_sort u ind.mind_sort in
  let ind_sort =
    match sub_temp, mib.mind_template with
    | Some sub_temp, Some temp -> Template.template_subst_sort sub_temp temp.template_concl
    | _, _ -> ind_sort
  in
  match ind_sort with
  | SProp -> return (None, sprop)
  | Prop -> return (None, prop)
  | Set ->
      let nu = sup_list (List.map snd fresh_sorts) Univ.Universe.type0 in
      if is_nested then begin
        let* sigma = get_sigma in
        let (sigma, lalg) = Evd.new_univ_level_variable UnivRigid sigma in
        let ualg = Univ.Universe.make lalg in
        let return_sort = sort_of_univ @@ Univ.Universe.sup nu ualg in
        (fun s -> return (Some (sort_of_univ ualg), return_sort) (update_sigma s sigma))
      end
      else
        return (None, sort_of_univ nu)
  | Type u ->
      let nu = sup_list (List.map snd fresh_sorts) u in
      if is_nested then begin
        let* sigma = get_sigma in
        let (sigma, lalg) = Evd.new_univ_level_variable UnivRigid sigma in
        let ualg = Univ.Universe.make lalg in
        let return_sort = sort_of_univ @@ Univ.Universe.sup nu ualg in
        (fun s -> return (Some (sort_of_univ ualg), return_sort) (update_sigma s sigma))
      end
      else
        return (None, sort_of_univ nu)
  | QSort (q,u) ->
      let nu = sup_list (List.map snd fresh_sorts) u in
      if is_nested then begin
        let* sigma = get_sigma in
        let (sigma, lalg) = Evd.new_univ_level_variable UnivRigid sigma in
        let ualg = Univ.Universe.make lalg in
        let return_sort = qsort q @@ Univ.Universe.sup nu ualg in
        (fun s -> return (Some (qsort q ualg), return_sort) (update_sigma s sigma))
      end
      else
        return (None, qsort q nu)

(** Add the inductive blocks in the context *)
let compute_return_sort kn u sub_temp mib uparams nuparams strpos fresh_sorts =
  array_mapi (fun pos_ind ind ->
      let rev = ERelevance.make ind.mind_relevance in
      let* ind_is_nested = is_nested_ind kn mib ind uparams nuparams strpos in
      let* (fu, sort) = compute_one_return_sort mib ind ind_is_nested u sub_temp fresh_sorts in
      let fu = Option.map (fun x -> mkSort @@ ESorts.make x) fu in
      let return_sort = mkSort @@ ESorts.make sort in
      return (fu, return_sort)
    ) mib.mind_packets

(** Generate the type of the sparse parametricity  *)
let gen_type_sparse_parametricity_param kn pos_ind u mib key_uparams key_nuparams return_sort =
  (* Closure uparams and predicates, nuparams and indices *)
  let ind = mib.mind_packets.(pos_ind) in
  let@ key_indices = closure_indices fid Prod Fresh naming_hd ind u in
  (* Bind the inductive *)
  let* rev_ind = ind_relevance ind u in
  let name_ind = make_annot Anonymous rev_ind in
  let* tind = make_ind ((kn, pos_ind), u) key_uparams key_nuparams key_indices in
  let@ key_VarMatch = make_binder fid Prod naming_hd_fresh name_ind tind in
  return return_sort

let gen_type_sparse_parametricity kn pos_ind u mib uparams strpos fresh_sorts nuparams return_sort =
    let@ (key_uparams, _, _) = closure_uparams_preds Prod uparams strpos fresh_sorts in
    let@ key_nuparams = closure_nuparams fid Prod naming_id nuparams in
    gen_type_sparse_parametricity_param kn pos_ind u mib key_uparams key_nuparams return_sort

(** Add the inductive blocks in the context *)
let add_inductive kn u mib return_sorts uparams strpos fresh_sorts nuparams cc =
  let* cxt = array_map2i (fun pos_ind ind return_sort ->
      let suff v = Id.of_string @@ Id.to_string v ^ "_all" in
      let sparam_name = Name (suff ind.mind_typename) in
      let rev = ERelevance.make ind.mind_relevance in
      let* ty = gen_type_sparse_parametricity kn pos_ind u mib uparams strpos fresh_sorts nuparams return_sort in
      return (LocalAssum (make_annot sparam_name rev, ty))
    ) mib.mind_packets return_sorts in
  add_context Fresh naming_id (List.rev @@ Array.to_list cxt) cc


(** {7 Generate the Type of the New Constructors } *)

(** Recursively compute the predicate, returns None if it is not nested *)
let compute_pred to_compute f i x : (constr option) t =
  if to_compute then
    let* (cxt, hd) = decompose_lambda_decls x in
    let@ key_loc = closure_context fopt Lambda Fresh naming_id cxt in
    (* create new variable *)
    let* sort = retyping_sort_of hd in
    let rev_x = relevance_of_sort sort in
    let name_var = make_annot Anonymous rev_x in
    (* let name_var = make_annot Anonymous ERelevance.relevant in *)
    let@ key_arg = make_binder fopt Lambda naming_id name_var hd in
    let* ty_var = State.get_type key_arg in
    (* compute rec call *)
    let* res = f key_arg ty_var in
    return @@ res
else return None

type ('a, 'b) sum = Left of 'a | Right of 'b

(** Compute the new argument *)
let rec make_rec_call_ty kn pos_ind mib rep_inds ((key_uparams, key_preds, key_uparams_preds) as key_up) strpos ualg key_arg ty : constr option t =
  let* (loc, hd) = view_arg kn mib key_uparams strpos ty in
  (* Compute the argument *)
  let@ key_locals = closure_context fopt Prod Fresh naming_id loc in
  let* arg = get_term key_arg in
  let* loc = get_terms key_locals in
  let  inst_arg = mkApp (arg, loc) in
  (* Match head *)
  match hd with
  | ArgIsSPUparam (pos_uparam, iargs) ->
      let pos_in_keys = up_to_spup pos_uparam strpos in
      let* pred_tm = geti_term key_preds pos_in_keys in
      let pred = mkApp (pred_tm, Array.concat [ iargs; [|inst_arg|] ]) in
      return @@ Some pred
  | ArgIsInd (pos_ind_block, inst_nuparams, inst_indices) ->
    begin
      let* inst_uparams_preds = get_terms key_uparams_preds in
      let ind_args = Array.concat [inst_uparams_preds; inst_nuparams; inst_indices; [|inst_arg|]] in
      match rep_inds with
      | Left key_inds -> let* ind = geti_term key_inds pos_ind in
                return @@ Some (mkApp (ind, ind_args))
      | Right (kn_nested, unested) ->
          return @@ Some (mkApp (mkIndU ((kn_nested, pos_ind), unested), ind_args))
    end
  | ArgIsNested (kn_nested, pos_nested, mib_nested, mib_nested_strpos, ind_nested,
                  inst_uparams, inst_nuparams_indices) ->
    begin
      (* eta expand arguments *)
      let uparams_nested = of_rel_context @@ fst @@ Declareops.split_uparans_nuparams mib_nested.mind_nparams_rec mib_nested.mind_params_ctxt in
      let* inst_uparams = eta_expand_instantiation inst_uparams uparams_nested in
      (* Compute the recursive predicates *)
      let compute_pred i x b = compute_pred b (fun a b ->
            make_rec_call_ty kn pos_ind mib rep_inds key_up strpos ualg a b) i x in
      let* rec_preds = array_map2i compute_pred inst_uparams (Array.of_list mib_nested_strpos) in
      (* If at least one argument is nested, lookup the sparse parametricity *)
      if Array.for_all Option.is_empty rec_preds then
        return None
      else begin
        match lookup_sparse_parametricity_only (kn, pos_ind) (kn_nested, pos_nested) with
        | None -> return None
        | Some ref_sparam ->
        (* Create: Indε A0 PA0 ... An PAn B0 ... Bm i0 ... il (arg a0 ... an) *)
        let* ref_ind = fresh_global ref_sparam in
        let* inst_uparams = instantiate_sparse_parametricity inst_uparams mib_nested_strpos rec_preds in
          (* arg a0 ... an *)
        let* arg = get_term key_arg in
        let* loc = get_terms key_locals in
        let arg = mkApp (arg , loc) in
        (* Instantiation *)
        let* _ = array_mapi (fun _ t -> print_term "arg is = " t) inst_uparams in
        let* rec_hyp = typing_checked_appvect ref_ind @@ Array.concat [inst_uparams; inst_nuparams_indices; [|arg|]] in
        (* Add constrains with return sort *)
        match ualg with
        | None -> return (Some rec_hyp)
        | Some ualg ->
        let* env = get_env in
        let* sigma = get_sigma in
        let ujud_rec_hyp = Retyping.get_judgment_of env sigma rec_hyp in
        let* env = get_env in
        let* sigma = get_sigma in
        let sigma = Typing.check_actual_type env sigma ujud_rec_hyp ualg in
        (* return *)
        let* s = get_state in
        (fun s -> return (Some rec_hyp) (update_sigma s sigma))
      end
    end
  | _ -> return None

(** Create and bind the recursive call *)
let make_rec_call_cc kn pos_ind mib key_inds ((key_uparams, key_preds, key_uparams_preds) as key_up) strpos ualg _ key_arg cc =
  let* ty_arg = State.get_type key_arg in
  let* rec_call = make_rec_call_ty kn pos_ind mib (Left key_inds) key_up strpos ualg key_arg ty_arg in
  match rec_call with
  | Some rec_hyp ->
      (* Compute the relevance after the instantiation *)
      let* env = get_env in
      let* sigma = get_sigma in
      let* rec_hyp_sort = retyping_sort_of rec_hyp in
      let rec_hyp_rev = relevance_of_sort rec_hyp_sort in
      let name_rec_hyp = make_annot Anonymous rec_hyp_rev in
      let@ _ = make_binder fid Prod naming_id name_rec_hyp rec_hyp in
      cc [key_arg]
  | _ -> cc [key_arg]

(** Closure of the args, and of the rec call if [rec_hyp], and if any *)
let closure_args_and_rec_call kn pos_ind mib key_inds key_up strpos ualg args =
  read_by_decl args
    (build_binder fid Prod Old naming_hd)
    (fun _ _ cc -> cc [])
    (make_rec_call_cc kn pos_ind mib key_inds key_up strpos ualg)

(** Generate the type of the constructors of sparse parametricity
    ∀ (uparams + preds), ∀ nuparams, ∀ [args + rec], Indε (UP+PRED) NUP IND (cst up nup args) *)
let gen_type_cst_sparse_param kn pos_ind u mib key_inds ((key_uparams, key_preds, key_uparams_preds) as key_up) strpos key_nuparams ualg pos_ctor ctor =
  (* Closure uparams and predicates, nuparams, args + hyp *)
  let* (args, indices) = get_args mib u ctor in
  let@ key_args = closure_args_and_rec_call kn pos_ind mib key_inds key_up strpos ualg args in
  (* Build the new inductive *)
  let* ind = geti_term key_inds pos_ind in
  let* inst_uparams_preds = get_terms key_uparams_preds in
  let* inst_nuparams = get_terms key_nuparams in
  let* inst_indices = array_mapi (fun _ -> weaken) indices in
  let ind = mkApp (ind, Array.concat [inst_uparams_preds; inst_nuparams; inst_indices]) in
  (* Builds the constructor *)
  let* k = get_terms key_args in
  let* cst = make_cst ((kn, pos_ind), u) pos_ctor key_uparams key_nuparams k in
  (* Return *)
  return @@ mkApp (ind, [|cst|])



  (** {7 Make Entries } *)

open Entries

let gen_one_ind_sparse_param kn pos_ind ind u mib return_sorts key_inds key_up strpos key_nuparams : one_inductive_entry t =
  let suff v = Id.of_string @@ Id.to_string v ^ "_all" in
  let sparam_name = suff ind.mind_typename in
  let sparam_ctors_name = Array.map suff ind.mind_consnames in
  let ulag, return_sort = return_sorts.(pos_ind) in
  let* sparam_type = gen_type_sparse_parametricity_param kn pos_ind u mib ((fun (a,_,_) -> a) key_up) key_nuparams return_sort in
  let* sparam_ctors_type = array_mapi (gen_type_cst_sparse_param kn pos_ind u mib key_inds key_up strpos key_nuparams ulag) ind.mind_nf_lc in
  let* sigma = get_sigma in
  return {
    mind_entry_typename = sparam_name ;
    mind_entry_arity = to_constr sigma sparam_type ;
    mind_entry_consnames = Array.to_list sparam_ctors_name;
    mind_entry_lc = Array.to_list @@ Array.map (to_constr sigma) sparam_ctors_type;
  }

let fresh_sort i =
  let open UState in
    let* sigma = get_sigma in
    let name_s = Id.of_string @@ "s" ^ string_of_int i in
    let sigma, q, u = Evd.new_sort_info ~name:name_s UnivRigid sigma in
    fun state -> return (q,u) (update_sigma state sigma)

let create_fresh_sorts_pred strpos =
  let nb_sorts = List.fold_right (fun a b -> a + b) (List.map Bool.to_int strpos) 0 in
  let init = List.make nb_sorts 0 in
  list_mapi (fun i _ -> fresh_sort i) init

let gen_sparse_parametricity_aux kn u sub_temp mib uparams strpos nuparams : mutual_inductive_entry t =
  (* create fresh sorts, return types, and add the inductives *)
  let* fresh_sorts = create_fresh_sorts_pred strpos in
  let* return_sorts = compute_return_sort kn u sub_temp mib uparams nuparams strpos fresh_sorts in
  let@ key_inds = add_inductive kn u mib (Array.map snd return_sorts) uparams strpos fresh_sorts nuparams in
  (*uparams + preds, nuparams and recover the context of parameters *)
  let@ key_up = context_uparams_preds uparams strpos fresh_sorts in
  let@ key_nuparams = add_context_nuparams naming_id nuparams in
  let* ctxt_params = get_context in
  let ctxt_params = fst @@ List.chop (List.length ctxt_params - Array.length mib.mind_packets) ctxt_params in
  (* create the inductive body *)
  let* ind_bodies = array_mapi (fun pos_ind ind ->
    gen_one_ind_sparse_param kn pos_ind ind u mib return_sorts key_inds key_up strpos key_nuparams) mib.mind_packets in
  let* sigma = get_sigma in
  (* build entry *)
  let mie =
  {
    mind_entry_record = None;
    mind_entry_finite = mib.mind_finite;
    mind_entry_params = EConstr.to_rel_context sigma ctxt_params ;
    mind_entry_inds = Array.to_list ind_bodies;
    mind_entry_universes = Polymorphic_ind_entry (Evd.to_universe_context sigma);
    mind_entry_variance = None;
    mind_entry_private = mib.mind_private;
  }
  in
  (* DEBUG *)
  let params = EConstr.of_rel_context mie.mind_entry_params in
  let ind = List.hd @@ mie.mind_entry_inds in
  let ind_ty = EConstr.of_constr @@ ind.mind_entry_arity in
  let ctors_ty = List.map EConstr.of_constr ind.mind_entry_lc in
  let* env = get_env in
  dbg Pp.(fun () -> str "Type Sparse Parametricity = " ++ (Termops.Internal.print_constr_env env sigma (it_mkProd_or_LetIn ind_ty params)) ++ str "\n");
  List.iteri (fun i ty_cst -> dbg Pp.(fun () -> str "TY CST_" ++ int i ++ str " = " ++ Termops.Internal.print_constr_env env sigma (it_mkProd_or_LetIn ty_cst params) ++ str "\n")) ctors_ty;
  let* sigma = get_sigma in
  let uv = Evd.ustate sigma in
  dbg Pp.(fun () -> str "EVAR MAP = " ++ UState.pr uv ++ str "\n");
  (* RETURN *)
  return mie


let gen_sparse_parametricity env sigma kn u mib =
  let (sigma, uparams, nuparams, sub_temp) = get_params_sep sigma mib u in
  let strpos = Positive_parameters.compute_params_rec_strpos env kn mib in
  (* dbg Pp.(fun () -> str "strpos = " ++ pp_lbool strpos); *)
  run env sigma @@ gen_sparse_parametricity_aux kn u sub_temp mib uparams strpos nuparams



(** {6 Generate the Local Fundamental Theorem for Sparse Parametricity } *)

let mkPredHold1 key_arg key_pred =
  let* arg_ty = State.get_type key_arg in
  let* (locs, hd) = whd_decompose_prod_decls arg_ty in
  let@ key_locs = closure_context fid Prod Fresh naming_hd locs in
  (* make args *)
  let* loc = get_terms key_locs in
  let* arg_tm = get_term key_arg in
  let arg = mkApp (arg_tm, loc) in
  (* relevance *)
  let* sigma = get_sigma in
  let sort = destSort sigma hd in
  let arg_rev = ESorts.relevance_of_sort sort in
  let name_hd = make_annot Anonymous arg_rev in
  (* bind *)
  let@ key_hd = build_binder fid Prod Fresh naming_hd @@ LocalAssum (name_hd, arg) in
  (* Return PA x1 ... xn a *)
  let* loc = get_terms key_locs in
  let* hd = get_term key_hd in
  let* pred = get_term key_pred in
  return @@ mkApp (pred, Array.concat [loc; [|hd|]])

let closure_uparams_preds_holds uparams strpos fresh_sorts cc =
  (* let open Sorts in *)
  let rec aux i key_uparams key_preds key_uparams_preds key_preds_hold tel cc =
    match tel with
    | [] -> cc (((List.rev key_uparams), (List.rev key_preds), (List.rev key_uparams_preds)), (List.rev key_preds_hold))
    | decl :: tel ->
        let@ key_up = build_binder fid Lambda Old naming_id decl in
        if (Option.has_some @@ get_value decl) then
          aux i key_uparams key_preds key_uparams_preds key_preds_hold tel cc
        else if not (List.nth strpos i) then
          aux (i+1) (key_up::key_uparams) key_preds (key_up::key_uparams_preds) key_preds_hold tel cc
        else
          (* create (PA : A -> s) *)
          let name = Name.map_id (fun id -> Id.of_string @@ "P" ^ Id.to_string id) (get_name decl) in
          let name_pred = make_annot name ERelevance.relevant in
          let pred_sort_info = List.nth fresh_sorts @@ up_to_spup i strpos in
          let* type_pred = mkPred key_up @@ mkSort @@ ESorts.make @@ (fun (a,b) -> Sorts.qsort a b) pred_sort_info in
          let@ key_pred = build_binder fid Lambda Fresh naming_id @@ LocalAssum (name_pred, type_pred) in
          (* create (HPA : forall a, PA a) *)
          let id_pred_hold = Name.map_id (fun id -> Id.of_string @@ "HP" ^ Id.to_string id) (get_name decl) in
          let pred_hold_sort = ERelevance.make @@ Sorts.relevance_of_sort @@ Sorts.qsort (fst pred_sort_info) (snd pred_sort_info) in
          let name_pred_hold = make_annot id_pred_hold pred_hold_sort in
          let* type_pred_hold = mkPredHold1 key_up key_pred in
          let@ key_pred_hold = build_binder fid Lambda Fresh naming_id @@ LocalAssum (name_pred_hold, type_pred_hold) in
          aux (i+1) (key_up::key_uparams) (key_pred::key_preds) (key_pred::key_up::key_uparams_preds) (key_pred_hold::key_preds_hold) tel cc
  in
  aux 0 [] [] [] [] (List.rev uparams) cc

let fresh_inductive_instance ind =
  let* env = get_env in
  let* sigma = get_sigma in
  let sigma, ((_, u) as pind) = Evd.fresh_inductive_instance env sigma ind in
  (fun s -> return (u, mkIndU pind)  (update_sigma s sigma))

let make_ind_fresh_instance (kn, pos_ind) key_uparams key_nuparams key_indices =
  let* env = get_env in
  let* sigma = get_sigma in
  let* (u, tInd) = fresh_inductive_instance (kn, pos_ind) in
  let* inst_ind = get_terms (key_uparams @ key_nuparams @ key_indices) in
  let* ind = typing_checked_appvect tInd inst_ind in
  return (ind,u)

let make_ccl_finstance kn_nested pos_ind key_uparams_preds key_nuparams key_indices key_VarMatch =
  let* (ccl, u) = make_ind_fresh_instance (kn_nested, pos_ind) key_uparams_preds key_nuparams (key_indices @ [key_VarMatch]) in
  return (ccl, Some u)

let make_ccl kn_nested pos_ind unested key_uparams_preds key_nuparams key_indices key_VarMatch =
  match unested with
  | None -> make_ind_fresh_instance (kn_nested, pos_ind) key_uparams_preds key_nuparams (key_indices @ [key_VarMatch])
  | Some unested ->
    let* ccl = make_ind ((kn_nested, pos_ind), unested) key_uparams_preds key_nuparams (key_indices @ [key_VarMatch]) in
    return (ccl, unested)

let return_type kn kn_nested pos_ind u mib key_uparams key_uparams_preds nuparams =
  let@ key_nuparams = closure_nuparams fleft Prod naming_id nuparams in
  (* Closure uparams and predicates, nuparams and indices *)
  let ind = mib.mind_packets.(pos_ind) in
  let@ key_indices = closure_indices fleft Prod Fresh naming_hd ind u in
  (* Bind the inductive *)
  let* rev_ind = ind_relevance ind u in
  let name_ind = make_annot Anonymous rev_ind in
  let* tind = make_ind ((kn, pos_ind), u) key_uparams key_nuparams key_indices in
  let@ key_VarMatch = make_binder fleft Prod naming_hd_fresh name_ind tind in
  (* Return the sort of the inductive *)
  make_ccl_finstance kn_nested pos_ind key_uparams_preds key_nuparams key_indices key_VarMatch

(* let gen_fundamental_theorem_type kn kn_nested focus u mib uparams strpos nuparams =
  let@ key_inds = add_context Old naming_id (add_ind mib) in
  let* fresh_sorts = create_fresh_sorts_pred strpos in
  let@ ((key_uparams, key_preds, key_uparams_preds) as key_up, key_preds_hold) = closure_uparams_preds_holds uparams strpos fresh_sorts in
  return_type kn kn_nested focus u mib key_uparams key_uparams_preds nuparams *)

let rec make_rec_call kn knu pos_ind mib ((key_uparams, _, _) as key_up) key_preds_hold key_fixs strpos key_arg ty : (constr option) State.t =
  let* (loc, v) = view_arg kn mib key_uparams strpos ty in
    (* inst argument *)
  let@ key_locals = closure_context fopt Lambda Fresh naming_id loc in
  let* arg_tm = get_term key_arg in
  let* loc = get_terms key_locals in
  let inst_arg = mkApp (arg_tm, loc) in
  (* check head *)
  match v with
    | ArgIsSPUparam (pos_uparam, iargs) ->
      let pos_in_keys = up_to_spup pos_uparam strpos in
      let* pred_hold_tm = geti_term key_preds_hold pos_in_keys in
      let* sigma = get_sigma in
      let rec_hyp = mkApp (pred_hold_tm, Array.concat [ iargs; [|inst_arg|] ]) in
      return @@ Some rec_hyp
  | ArgIsInd (pos_ind_block, inst_nuparams, inst_indices) ->
    (* generate recursion hypotheses only for the blocks that are used *)
        (* Fi B0 ... Bm i0 ... il (x a0 ... an) *)
        let* fix = geti_term key_fixs pos_ind_block in
        return @@ Some (mkApp (fix, Array.concat [inst_nuparams; inst_indices; [|inst_arg|]]))
  | ArgIsNested (kn_nested, pos_nested, mib_nested, mib_nested_strpos, ind_nested,
                  inst_uparams, inst_nuparams_indices) ->
      begin
        (* eta expand arguments *)
        let uparams_nested = of_rel_context @@ fst @@ Declareops.split_uparans_nuparams mib_nested.mind_nparams_rec mib_nested.mind_params_ctxt in
        let* inst_uparams = eta_expand_instantiation inst_uparams uparams_nested in
        (* Compute the recursive predicates, and their proofs *)
        let compute_pred_preds i x b = compute_pred b (make_rec_call_ty kn pos_ind mib (Right knu) key_up strpos (Obj.magic ())) i x in
        let* rec_preds = array_map2i compute_pred_preds inst_uparams (Array.of_list mib_nested_strpos) in
        let compute_pred_holds i x b = compute_pred b (make_rec_call kn knu pos_ind mib key_up key_preds_hold key_fixs strpos) i x in
        let* rec_preds_hold = array_map2i compute_pred_holds inst_uparams (Array.of_list mib_nested_strpos) in
        (* If at least one argument is nested, lookup the local fundamental theorem *)
        if Array.for_all Option.is_empty rec_preds_hold then return None else begin
        match lookup_sparse_parametricity (kn, pos_ind) (kn_nested, pos_nested) with
        | None -> return None
        | Some (_, ref_fth) ->
        (* fth A0 PA0 HPA0 ... An PAn HPAn B0 ... Bm i0 ... il (arg a0 ... an) *)
        let* fth = fresh_global ref_fth in
        let* inst_uparams = instantiate_fundamental_theorem inst_uparams mib_nested_strpos rec_preds rec_preds_hold in
        (* Instantiation *)
        let* rec_hyp = typing_checked_appvect fth (Array.concat [inst_uparams; inst_nuparams_indices; [|inst_arg|] ]) in
        return @@ Some (rec_hyp)
        end
      end
  | _ -> return None

let compute_args_fix kn knu pos_ind mib key_up key_preds_hold key_fixs strpos key_args =
  CList.fold_right_i (fun pos_arg key_arg acc ->
    let* acc = acc in
    let* tm_arg = get_term key_arg in
      let* ty_arg = State.get_type key_arg in
      let* rec_call = make_rec_call kn knu pos_ind mib key_up key_preds_hold key_fixs strpos key_arg ty_arg in
      match rec_call with
        | Some rc_tm -> return @@ tm_arg :: rc_tm :: acc
        | None -> return @@ tm_arg :: acc
  ) 0 key_args (return [])

let make_cst_typing ((kn, pos_ind), u) pos_ctor key_uparams key_nuparams args =
  let tCst = mkConstructU (((kn, pos_ind), 1+pos_ctor), u) in
  let* params = get_terms (key_uparams @ key_nuparams) in
  typing_checked_appvect tCst (Array.concat [params; args])

let gen_fundamental_theorem_aux kn kn_nested focus u mib uparams strpos nuparams : constr t =
  (* 1. Create fresh sorts + new unfiform parameters *)
  let* fresh_sorts = create_fresh_sorts_pred strpos in
  let@ ((key_uparams, key_preds, key_uparams_preds) as key_up, key_preds_hold) = closure_uparams_preds_holds uparams strpos fresh_sorts in
  (* 2. Fixpoint *)
  let fix_name pos_ind ind = make_annot (Name (Id.of_string "F")) (relevance_of_sort @@ ESorts.make ind.mind_sort) in
  let fix_type pos_ind ind = return_type kn kn_nested pos_ind u mib key_uparams key_uparams_preds nuparams in
  let fix_rarg pos_ind ind = (mib.mind_nparams - mib.mind_nparams_rec) + ind.mind_nrealargs in
  let is_rec = Array.length mib.mind_packets > 1 || (Inductiveops.mis_is_recursive mib.mind_packets.(0)) in
  let@ (key_fixs, pos_ind, ind, unested) =
    (* Doe not create a fix if it is not-recursive and only has one inductive body *)
    if is_rec
    then make_fix (Array.to_list mib.mind_packets) focus fix_rarg fix_name fix_type
    else fun cc -> cc ([], 0, mib.mind_packets.(0), None)
  in
    (* 3. Closure Nuparams / Indices / Var *)
  let@ key_nuparams = closure_nuparams fid Lambda naming_id nuparams in
  let ind = mib.mind_packets.(pos_ind) in
  let@ key_indices = closure_indices fid Lambda Fresh naming_hd ind u in
  let* rev_ind = ind_relevance ind u in
  let name_ind = make_annot Anonymous rev_ind in
  let* tind = make_ind ((kn, pos_ind), u) key_uparams key_nuparams key_indices in
  let@ key_VarMatch = make_binder fid Lambda naming_hd_fresh name_ind tind in
  (* 4 Match to prove P ... x *)
  let case_pred = make_ccl kn_nested pos_ind unested key_uparams_preds key_nuparams in
  let* inst_params = get_terms (key_uparams @ key_nuparams )in
  let* var_match = get_term key_VarMatch in
  let* inst_indices = get_terms key_indices in
  let@ (key_args, _, _, pos_ctor, unested) =
    make_case_or_projections naming_hd_fresh mib (kn, pos_ind) ind u key_uparams key_nuparams inst_params
      inst_indices case_pred (relevance_of_sort @@ ESorts.make ind.mind_sort) var_match in
  (* 5 Body of the branch *)
  let* args = compute_args_fix kn (kn_nested, unested) pos_ind mib key_up key_preds_hold key_fixs strpos key_args in
  make_cst_typing ((kn_nested, pos_ind), unested) pos_ctor key_uparams_preds key_nuparams (Array.of_list args)

let gen_fundamental_theorem env sigma kn kn_nested focus u mib =
  let (sigma, uparams, nuparams, _) = get_params_sep sigma mib u in
  let strpos = Positive_parameters.compute_params_rec_strpos env kn mib in
  dbg Pp.(fun () -> str "strpos = " ++ pp_lbool strpos);
  let (sigma, tm) = run env sigma @@ gen_fundamental_theorem_aux kn kn_nested focus u mib uparams strpos nuparams in
  (* let (_, ty) = run env sigma @@ gen_fundamental_theorem_type kn kn_nested focus u mib uparams strpos nuparams in *)
  dbg Pp.(fun () -> str "Fundamental Theorem = " ++ Termops.Internal.print_constr_env env sigma tm ++ str "\n");
  let uv = Evd.ustate sigma in
  (* dbg Pp.(fun () -> str "EVAR MAP = " ++ UState.pr uv ++ str "\n\n"); *)
  let uv = UState.collapse_above_prop_sort_variables ~to_prop:true uv in
  let uv = UState.normalize_variables uv in
  let uv = UState.minimize uv in
  dbg Pp.(fun () -> str "MIN EVAR MAP = " ++ UState.pr uv ++ str "\n");
  dbg Pp.(fun () -> str "---------------------------------------- \n\n");
  (sigma, tm)
