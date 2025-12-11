(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open EConstr
open Inductiveops

(* This represents how a term is getting extracted from another term *)
type term_extraction =
| Id
(* the constructor from which to extract, type of the constructor that is getting extracted, index (1 based) to extract from, further extraction *)
| Extraction of ((constructor * EInstance.t) * EConstr.t * int * term_extraction)

(* this represents how a term is getting composed from an inductive type *)
type term_composition =
(* env type to compose *)
| FromEnv of EConstr.t
(* env type to compose, env parameter term to extract from, index (1 based) of parameter, extraction for the given type*)
| FromParameter of EConstr.t * EConstr.t * int * term_extraction
(* env type to compose, index (1 based) index to compose from, extraction for the given type *)
| FromIndex of EConstr.t * int * term_extraction
(* composition for f, array of composition for arg *)
| Composition of term_composition * term_composition array

type projection_type =
(* simply typed fields *)
| Simple
(* dependently typed fields for wich a type term_composition exists *)
| Dependent_Extractable of term_composition
(* dependently typed fields for which currently no projection generation is known, simply typed generation is getting tried anyways *)
| NotProjectable

(*get the ith (1 based) argument in a series of prods*)
let get_ith_arg sigma i term =
  let (rels_to_arg, rest) = decompose_prod_n sigma (i-1) term in
  let (arg_name, arg_type,rest) = destProd sigma rest in
  (rels_to_arg, (arg_name, arg_type), rest)

(*determin if the ith (1 based real constructor arguments without parametes) field of a constructor depends on its other fields*)
let is_field_i_dependent env sigma cnstr i =
  let constructor_type = e_type_of_constructor env sigma cnstr in
  let ind_n_params = inductive_nparams env (fst (fst cnstr)) in
  let (_, (_, field_type), _) = get_ith_arg sigma (i + ind_n_params) constructor_type in
  not (Vars.noccur_between sigma 1 (i - 1) field_type)

(*this builds a projection in the simply typed case*)
let build_simple_projection env sigma intype cnstr special default =
  let open Context in
  let ci = (snd (fst cnstr)) in
  let body = Combinators.make_selector env sigma ~pos:ci ~special ~default (mkRel 1) intype in
  let id = Id.of_string "t" in
  mkLambda (make_annot (Name id) ERelevance.relevant, intype, body)

let (let*) m f = match m with
| None -> None
| Some x -> f x

(*find a composition to form a given term by extracting from given terms*)
let find_term_composition env sigma cnstr argindex env_field_type ind env_ind_params env_ind_args =
  (*first we need to get some information about the inductive type*)
  let env_ind_n_params = Array.length env_ind_params in
  let rel_type_of_constructor = type_of_constructor env cnstr in
  let (_, (_, rel_field_type), rel_field_rest) = get_ith_arg sigma (argindex+env_ind_n_params) rel_type_of_constructor in
  let (rel_target_context, rel_target_type) = decompose_prod sigma rel_field_rest in
  let rel_field_type_lifted = Vars.lift (List.length rel_target_context + 1) rel_field_type in
  let (_, rel_args) = decompose_app sigma rel_target_type in
  let (rel_ind_params, rel_ind_args) = CArray.chop env_ind_n_params rel_args in
  (*the actual recursive search for the term_composition*)
  let rec find_term_composition_rec env sigma rel_term_to_compose env_term_to_compose =
    if isRef sigma rel_term_to_compose then
      Some (FromEnv rel_term_to_compose)
    else match find_arg env sigma rel_term_to_compose rel_ind_params env_ind_params with
    | Some (i, extraction) ->
      Some (FromParameter (env_term_to_compose, env_ind_params.(i-1), i, extraction))
    | None ->
      begin match find_arg env sigma rel_term_to_compose rel_ind_args env_ind_args with
      | Some (i, extraction) ->
        Some (FromIndex (env_term_to_compose, i, extraction))
      | None ->
        begin match EConstr.kind sigma rel_term_to_compose with
        | App (rel_f,rel_args) ->
          let (env_f,env_args) = decompose_app sigma env_term_to_compose in
          let* f_composition = find_term_composition_rec env sigma rel_f env_f in
            if Array.length env_args != Array.length rel_args then
              None
            else
              let* args_compositions =
                let exception ArgNotComposable in
                let map i rel_arg =
                  let arg_composition = find_term_composition_rec env sigma rel_arg env_args.(i) in
                  match arg_composition with
                  | Some arg_composition -> arg_composition
                  | None -> raise ArgNotComposable
                in
                try Some (CArray.mapi map rel_args) with ArgNotComposable -> None
              in
              Some (Composition (f_composition, args_compositions))
        | _ -> None
      end
    end

  (*finds the first argument from which a term can be extracted*)
  and find_arg env sigma term_to_extract terms_to_extract_from env_types_of_fields =
    let find (i, term_to_extract_from) =
      let* r = find_term_extraction env sigma term_to_extract term_to_extract_from env_types_of_fields.(i) in
      Some (i + 1, r)
    in
    let rec seq_find_map xs = match xs() with
    | Seq.Nil -> None
    | Seq.Cons(x,xs) ->
      match find x with
      | None -> seq_find_map xs
      | Some _ as result -> result
    in
    seq_find_map (Array.to_seqi terms_to_extract_from)

  (*finds the term_extraction for a given term*)
  and find_term_extraction env sigma term_to_extract term_to_extract_from type_of_term_to_extract_from =
    if eq_constr_nounivs sigma term_to_extract term_to_extract_from then
      Some Id
    else match EConstr.kind sigma term_to_extract_from with
    | App (f, args) ->
      begin match EConstr.kind sigma f with
      | Construct c ->
        let (_, env_args) = decompose_app sigma type_of_term_to_extract_from in
        let* (i, extraction_result) = find_arg env sigma term_to_extract args env_args in
        Some (Extraction (c, type_of_term_to_extract_from, i, extraction_result))
      | _ -> None
      end
    | _ -> None
  in
  find_term_composition_rec env sigma rel_field_type_lifted env_field_type

(*tests if a field is projectable and returns the type_composition if it is*)
let projectability_test env sigma cnstr argindex field_type ind ind_params ind_args =
  let dependent = is_field_i_dependent env sigma cnstr argindex in
  if dependent then
    let composition = find_term_composition env sigma cnstr argindex field_type ind ind_params ind_args in
    match composition with
    | Some composition -> Dependent_Extractable composition
    | None -> NotProjectable
  else Simple

(*builds the term of a given term_extraction*)
let rec build_term_extraction env sigma default rel_term_to_extract_from env_term_to_extract_from extraction =
  match extraction with
  | Id -> rel_term_to_extract_from
  (* The term that is getting extracted, the term from wich its getting extracted, The constructor from which zu extract, index (1 based without params) to extract from, further extraction *)
  | Extraction ((cnstr, _), env_next_term_to_extract_from, index, next_extraction) ->
    let cnstr_n_args = constructor_nrealargs env cnstr in
    let special = build_term_extraction env sigma default (mkRel (cnstr_n_args-(index-1))) env_next_term_to_extract_from next_extraction in
    let pos = snd cnstr in
    let (_, match_type) = Typing.type_of env sigma env_term_to_extract_from in
    Combinators.make_selector env sigma ~pos ~special ~default rel_term_to_extract_from match_type

(*builds the term of a given term_composition*)
let rec build_term_composition env sigma term_composition ind_params n_ind_params ind_args n_ind_args =
  match term_composition with
  (* type to compose *)
  | FromEnv env_type_to_compose -> env_type_to_compose
  (* type to compose, parameter term to extract from, index (1 based) of parameter, extraction for the given type*)
  | FromParameter (env_type_to_compose, env_parameter_to_extract_from, parameter_index, extraction) ->
    let type_to_extract_from = ind_params.(parameter_index-1) in
    build_term_extraction env sigma env_type_to_compose env_parameter_to_extract_from type_to_extract_from extraction
  (* type to compose, indec term to extract from, index (1 based) index to compose from, extraction for the given type *)
  | FromIndex (env_type_to_compose, index_index, extraction) ->
    let type_to_extract_from = ind_args.(index_index-1) in
    build_term_extraction env sigma env_type_to_compose (mkRel (n_ind_args-(index_index-1))) type_to_extract_from extraction
  (* (f type to compose, composition for f), array of (arg type to compose, composition for arg)*)
  | Composition (f_composition,  arg_compositions) ->
    let f_extraction_term = build_term_composition env sigma f_composition ind_params n_ind_params ind_args n_ind_args in
    let map arg_composition = build_term_composition env sigma arg_composition ind_params n_ind_params ind_args n_ind_args in
    let arg_extraction_terms = Array.map map arg_compositions in
    mkApp (f_extraction_term, arg_extraction_terms)

(*replaces all rel variables corresponding to indices in a match statment with the index definition in the inductive definition*)
let match_indices env sigma cnst_summary term_to_match n_ind_args max_free_rel =
  let rec replace_rec n t = match EConstr.kind sigma t with
  | Rel i ->
    if i <= n_ind_args + n && i > n then
      cnst_summary.cs_concl_realargs.(n_ind_args-i)
    else t
  | _ -> EConstr.map_with_binders sigma (fun n -> n+1) replace_rec n t
  in
  EConstr.map_with_binders sigma (fun n -> n+1) replace_rec 0 term_to_match

let make_annot_numbered s i r =
  Context.make_annot (Name.mk_name (Nameops.make_ident s i)) r

(*makes a match statement where the index variables in the branches get replaced by the index definitions inside the inductive definition*)
let make_selector_match_indices env sigma ~pos ~special c (ind_fam, ind_args) return_type composition_type_template =
  let n_ind_args = List.length ind_args in
  let indt = IndType (ind_fam, ind_args) in
  let (ind, _),_ = dest_ind_family ind_fam in
  let () = Tacred.check_privacy env ind in
  let _, mip = Environ.lookup_mind_specif env ind in
  let deparsign = make_arity_signature env sigma true ind_fam in
  let p = it_mkLambda_or_LetIn return_type deparsign in
  let cstrs = get_constructors env ind_fam in
  let build_branch i =
    let max_free_rel = Option.default 0 (Int.Set.max_elt_opt (Termops.free_rels sigma composition_type_template)) in
    let matched_template = match_indices env sigma cstrs.(i-1) composition_type_template n_ind_args max_free_rel in
    let endpt = if Int.equal i pos then
      mkLambda (Context.make_annot Name.Anonymous ERelevance.relevant, matched_template, Vars.lift 1 special)
    else
      mkLambda (make_annot_numbered "t" None ERelevance.relevant, matched_template, mkRel 1)
    in
    let args = cstrs.(i-1).cs_args in
    it_mkLambda_or_LetIn endpt args
  in
  let brl =
    List.map build_branch(CList.interval 1 (Array.length mip.mind_consnames)) in
  let rci = ERelevance.relevant in (* TODO relevance *)
  let ci = make_case_info env ind RegularStyle in
  make_case_or_project env sigma indt ci (p, rci) c (Array.of_list brl)

(*builds a projection in the dependently typed case where a term_composition was found for the fields type*)
let build_dependent_projection_with_term_composition env sigma cnstr default special argty term_composition ((ind, ind_params) as ind_fam) ind_args =
  let n_ind_params = List.length ind_params in
  let n_ind_args = List.length ind_args in
  let composition_type_template = build_term_composition env sigma term_composition (Array.of_list ind_params) n_ind_params (Array.of_list ind_args) n_ind_args in
  let return_type = Vars.lift 1 (
    mkProd (Context.make_annot Name.Anonymous ERelevance.relevant, composition_type_template, Vars.lift 1 composition_type_template)
  ) in
  let e_match = make_selector_match_indices  env sigma ~pos:(snd (fst cnstr)) ~special (mkRel 1) (make_ind_family ind_fam, ind_args) return_type composition_type_template in
  let match_default = mkApp (e_match, [|default|]) in
  let proj = mkLambda (make_annot_numbered "e" None ERelevance.relevant, argty, match_default) in
  proj

(*checks the projectability of the given field and builds the according projection. If the field is found to be NotProjectable the simply typed projection generation is tried*)
let build_projection env sigma
  cnstr (*constructor that is getting projected*)
  argindex (*1 based index of the field to project counted from left without induction params*)
  field_type (*type of the field that gets projected*)
  default (*p.p_lhs so the thing inside the constructor*)
  special (*Rel (nargs-argind+1) so the debrujin index of the field to project directly after binding*)
  argty (*type of the constructor term that is getting projected*) =
  let IndType (ind_family,ind_args) =
    try find_rectype env sigma argty
    with Not_found ->
      CErrors.user_err
        Pp.(str "Cannot discriminate on inductive constructors with \
                 dependent types.") in
  let (ind, ind_params) = dest_ind_family ind_family in
  let cnstr = (fst cnstr, EInstance.make (snd cnstr)) in
  let proj_result = projectability_test env sigma cnstr argindex field_type ind (Array.of_list ind_params) (Array.of_list ind_args) in
  match proj_result with
  | Simple | NotProjectable ->
    let p = build_simple_projection env sigma argty cnstr special default in
    sigma, p
  | Dependent_Extractable type_composition ->
    let p = build_dependent_projection_with_term_composition env sigma cnstr default special argty type_composition (ind, ind_params) ind_args in
    sigma, p
