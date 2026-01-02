(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Declarations
open Util
open Names
open Constr
open Vars
open Environ
open Reduction
open Context.Rel.Declaration
open Pp

(** {6 Strictly Positive Uniform Parameters } *)

let dbg_strpos = CDebug.create ~name:"strpos" ()

let rec pp_list f l = match l with
  | []   -> Pp.str "]"
  | [a]  -> f a ++ Pp.str "]"
  | a::l -> f a ++ str "; " ++ pp_list f l

let pp_strpos l = Pp.str "[" ++ pp_list Pp.bool l

(** [&&] pointwise for lists *)
let andl = List.map2 (fun a b -> a && b)

(** Iterate [&&] on [f x] for an array [ar] *)
let andl_array f default ar =
  Array.fold_right (fun x acc -> andl acc (f x)) ar default

(** Check which uniform parameters are arity, unfolding Let-ins, and returns
    the updated environment and the initial value of strictly positivity     *)
let init_value env uparams =
  let rec aux env (tel : Constr.rel_context) =
    match tel with
    | [] -> (env, [])
    | decl::tel ->
      match get_value decl with
      | Some _ -> aux (push_rel decl env) tel
      | None   -> let ty = Reduction.whd_all env (get_type decl) in
                  let (env, init_value) = aux (push_rel decl env) tel in
                  (env, Term.isArity ty :: init_value)
    in
    aux env (List.rev uparams)

(** Check if the uniform parameters appear in a term *)
let check_strpos env uparams t =
  let nenv = List.length @@ Environ.rel_context env in
  let rec aux i tel =
    match tel with
    | [] -> []
    | decl::tel ->
      match get_value decl with
      | Some _ -> aux (i+1) tel
      | None   -> noccur_between (nenv - i) 1 t :: aux (i+1) tel
  in
  aux 0 (List.rev uparams)

(** Check if the uniform parameters appear in a context  *)
let check_strpos_context env uparams default cxt =
  let rec aux env strpos tel =
    match tel with
    | [] -> (env, strpos)
    | decl::tel ->
        match get_value decl with
        | Some _ -> aux (push_rel decl env) strpos tel
        | None   ->
          let ty = whd_all env @@ get_type decl in
          let strpos_decl = check_strpos env uparams ty in
          aux (push_rel decl env) (andl strpos_decl strpos) tel
  in aux env default (List.rev cxt)

(** Computes which uniform parameters are strictly positive in an argument *)
let rec compute_params_rec_strpos_arg compute_params_rec_strpos env kn uparams
          nparams_rec nparams init_value (arg : constr) : bool list =
  (* strictly positive uniform parameters do not appear on the left of an arrow *)
  let (local_vars, hd) = Reduction.whd_decompose_prod_decls env arg in
  let (env, strpos_local) = check_strpos_context env uparams init_value local_vars in
  (* check the head *)
  let (hd, inst_args) = decompose_app hd in
  let srpos_hd = match kind hd with
    | Rel k ->
        (* Check if it is the inductive *)
        if List.length (Environ.rel_context env) < k
        (* If it is the inductive, then they should not appear in the instantiation
        of the non-unfiform parameters and indices of the inductive type being defined *)
        then let (_, iargs) = Array.chop nparams_rec inst_args in
             andl_array (check_strpos env uparams) init_value iargs
        (* Otherwise, they should not appear in the arguments *)
        else andl_array (check_strpos env uparams) init_value inst_args
    | Ind ((kn_nested, _), _) ->
        (* Check if it is the inductive or nested *)
        if QMutInd.equal env kn kn_nested
        (* If it is the inductive, then they should not appear in the instantiation
          of the non-unfiform parameters and indices of the inductive type being defined *)
        then let (_, iargs) = Array.chop nparams_rec inst_args in
             andl_array (check_strpos env uparams) init_value iargs
        (* For nested arguments, they should: *)
        else begin
          let mib_nested = lookup_mind kn_nested env in
          let mib_nested_strpos = compute_params_rec_strpos env kn_nested mib_nested in
          let (inst_uparams, inst_nuparams_indices) = Array.chop mib_nested.mind_nparams_rec inst_args in
          let uparams_nested = List.rev @@ fst @@
                Context.Rel.chop_nhyps mib_nested.mind_nparams_rec @@
                List.rev mib_nested.mind_params_ctxt in
          let inst_uparams = eta_expand_instantiation env inst_uparams uparams_nested in
          (* - appear strictly positively in the instantiation of the uniform parameters
               that are strictly postive themselves
             - not appear in uniform parameters that are not strictly postive *)
          let strpos_inst_uparams = Array.fold_right_i (fun i x acc ->
            if List.nth mib_nested_strpos i
            then andl acc @@ compute_params_rec_strpos_arg compute_params_rec_strpos env kn uparams nparams_rec nparams init_value x
            else andl acc @@ check_strpos env uparams x
            ) inst_uparams init_value  in
          (* - not appear in the instantiation of the non-uniform parameters and indices *)
          let strpos_inst_nuparams_indices = andl_array (check_strpos env uparams) init_value inst_nuparams_indices in
          andl strpos_inst_uparams strpos_inst_nuparams_indices
        end
    | _ -> check_strpos env uparams hd
  in
  andl strpos_local srpos_hd

(** Computes which uniform parameters are strictly positive in a constructor *)
let compute_params_rec_strpos_ctor compute_params_rec_strpos env kn uparams nparams_rec nparams init_value (args, hd) =
  (* They must not appear on the left of an arrow in each argument *)
  let (env, strpos_args) =
    List.fold_right (
        fun arg (env, acc) ->
        match get_value arg with
        | Some _ -> (push_rel arg env, acc)
        | None   ->
            let strpos_arg = compute_params_rec_strpos_arg compute_params_rec_strpos
                                env kn uparams nparams_rec nparams init_value (get_type arg) in
          (push_rel arg env, andl acc strpos_arg)
      ) args (env, init_value)
  in
  (* They must not appear in the instantiation of the indices *)
  let (_, xs) = decompose_app hd in
  let inst_indices = Array.sub xs nparams (Array.length xs - nparams) in
  let str_inst_indices = andl_array (check_strpos env uparams) strpos_args inst_indices in
  let res_ctor = andl strpos_args str_inst_indices in
  res_ctor

(** Computes which uniform parameters are strictly positive in an inductive block *)
let compute_params_rec_strpos_ind compute_params_rec_strpos env kn uparams nparams_rec nparams init_value (indices, ctors) =
  (* They must not appear in indices *)
  let (_, strpos_indices) = check_strpos_context env uparams init_value indices in
  (* They must be strictly positive in each constructor *)
  let strpos_ctors = andl_array (compute_params_rec_strpos_ctor compute_params_rec_strpos
        env kn uparams nparams_rec nparams init_value) init_value ctors in
  let res_ind = andl strpos_indices strpos_ctors in
  res_ind

(** Computes which uniform parameters are strictly positive in a mutual inductive block.
    [inds : (rel_context * (rel_declaration list * types) array) array] contains
    the context of indices, then for each constructor the telescope of arguments, and the hd.
    This function can be used whether the inductive is refered using [Rel] or [Ind].
    This particular data representation is the one of indtypes.
    *)
let compute_params_rec_strpos_aux compute_params_rec_strpos env kn uparams nuparams nparams_rec nparams inds : bool list =
  if nparams_rec = 0 then [] else
  (* They must be arities [forall ..., sort X] *)
  let (env, init_value) = init_value env uparams in
  (* They must not appear in non-uniform parameters *)
  let (env, strpos_nuparams) = check_strpos_context env uparams init_value nuparams in
  (* They must be strictly positive in each inductive block *)
  let strpos_inds = andl_array (compute_params_rec_strpos_ind compute_params_rec_strpos
        env kn uparams nparams_rec nparams init_value) init_value inds in
  let res = andl strpos_nuparams strpos_inds in
  dbg_strpos (fun () -> MutInd.print kn ++ str ": Final Result = " ++ pp_strpos res);
  res

let rec compute_params_rec_strpos env kn (mib : mutual_inductive_body) : bool list =
  (* reset the context *)
  let env = set_rel_context_val empty_rel_context_val env in
  (* compute the data expected *)
  let inds = Array.map (fun ind ->
      let (indices, _) = List.chop (List.length ind.mind_arity_ctxt - mib.mind_nparams) ind.mind_arity_ctxt in
      let ctors = Array.map (fun (args, hd) ->
                      let (args,_) = List.chop (List.length args - mib.mind_nparams) args in
                      (args, hd)
                    ) ind.mind_nf_lc
                  in
      (indices, ctors)
    ) mib.mind_packets
  in
  let (uparams, nuparams) = map_pair List.rev @@ Context.Rel.chop_nhyps mib.mind_nparams_rec @@
                            List.rev mib.mind_params_ctxt in
  compute_params_rec_strpos_aux compute_params_rec_strpos env kn uparams nuparams mib.mind_nparams_rec mib.mind_nparams inds


  (** {6 Lookup All Predicate and its Theorem } *)

(** Suffix and register key for the [all] predicate and its theorem  *)
let default_suffix = (("_all", "_all_forall"), ("All", "AllForall"))

let rec bool_list_to_string lb =
  match lb with
  | [] -> ""
  | true::l  -> "1" ^ bool_list_to_string l
  | false::l -> "0" ^ bool_list_to_string l

(** Suffix and register key for partial version of the [all] predicate and its theorem  *)
let partial_suffix strpos =
  let ((a, b), (c, d)) = default_suffix in
  let s = "_" ^ bool_list_to_string strpos in
  ((a^s, b^s), (c^s, d^s))

(** Check a list of boolean is included in an other for [false <= true] *)
let rec inclusion_bool_list l l' =
  match l, l' with
  | [], [] -> true
  | false :: l, _ :: l' -> inclusion_bool_list l l'
  | true :: l, true :: l' -> inclusion_bool_list l l'
  | _, _ -> false

(** Compute the default positivity of the uniform parameters, and generates the suffix
    for naming the [all] predicate, and its theorem, as well as the key for registering.
    If a positivity specification is given by users [bool list option], it is
    checked to be included in the default one, and the suffix are modified accordingly. *)
let compute_positive_uparams_and_suffix env kn mib user_strpos =
  let default_strpos = compute_params_rec_strpos env kn mib in
  match user_strpos with
  | None -> (default_strpos, fst default_suffix, snd default_suffix)
  | Some user_strpos ->
      if inclusion_bool_list user_strpos default_strpos
      then let partial_suffix = partial_suffix user_strpos in
           (user_strpos, fst partial_suffix, snd partial_suffix)
      else CErrors.user_err Pp.(
          hov 0 (
               strbrk "The user-given uniform parameters allowed to nested on "
            ++ str "[" ++ prlist_with_sep (fun () -> str ", ") bool user_strpos ++ str "]"
            ++ strbrk " are not included in the ones that can acutally be nested on "
            ++ str "[" ++ prlist_with_sep (fun () -> str ", ") bool default_strpos ++ str "]"
          ))

(** Warning for looking up the [all] predicate and its theorem  *)
let warn_lookup_not_found =
  CWarnings.create ~name:("register_all") ~category:Deprecation.Version.v9_2
  Pp.(fun (key, ind, ind_nested) ->
    hov 0 (
         Nametab.XRefs.pr (TrueGlobal (IndRef ind))
      ++ strbrk " is nested using "
      ++ Nametab.XRefs.pr (TrueGlobal (IndRef ind_nested))
      ++ strbrk "."
      ++ strbrk "No lemma for "
      ++ Nametab.XRefs.pr (TrueGlobal (IndRef ind_nested))
      ++ strbrk " is registered for "
      ++ strbrk key ++  str "."
    ))

(** Lookup the [all] predicate, and its theorem *)
let lookup_all_theorem_aux ind ind_nested =
  let (_, (pred, thm)) = default_suffix in
  match DeclareScheme.lookup_scheme_opt pred ind_nested with
  | None -> warn_lookup_not_found (pred, ind, ind_nested); None
  | Some ref_pred ->
      match DeclareScheme.lookup_scheme_opt  thm ind_nested with
      | None -> warn_lookup_not_found (thm, ind, ind_nested); None
      | Some ref_thm -> Some (false, ref_pred, ref_thm)

(** Lookup the partial [all] predicate and its theorem for [ind_nested] for [args_are_nested].
    If they are not found, lookup the general [all] predicate and its theorem.
    Returns if the partial [all] was found, and the global references.
    Raise a warning if none is found. *)
let lookup_all_theorem ind ind_nested args_are_nested =
  let (_, (pred, thm)) = partial_suffix args_are_nested in
  match DeclareScheme.lookup_scheme_opt  pred ind_nested with
  | None -> lookup_all_theorem_aux ind ind_nested
  | Some ref_pred ->
      match DeclareScheme.lookup_scheme_opt  thm ind_nested with
      | Some ref_thm -> Some (true, ref_pred, ref_thm)
      | None -> warn_lookup_not_found (thm, ind,ind_nested);
                lookup_all_theorem_aux ind ind_nested


  (** {6 Instantiate the All Predicate and its Theorem } *)

open EConstr
open Inductive
open LibBinding
open State

let (let@) x f = x f
let (let*) x f = State.bind x f

let mkFunUnit x =
  let@ _ = rebind fid Lambda Fresh naming_id x in
  return @@ mkRef ((Rocqlib.lib_ref "core.unit.type"), EInstance.empty)

let instantiate_all_uparams partial_nesting strpos inst_uparams inst_preds =
  let inst_preds = Array.to_list inst_preds in
  let inst_uparams = Array.to_list inst_uparams in
  let* s = get_state in
  let inst_sparam =
    List.fold_right (fun (positive, inst_uparam, pred) acc ->
      if not positive then inst_uparam :: acc else
      match pred with
      | Some pred -> inst_uparam :: pred :: acc
      | None -> if partial_nesting
                then inst_uparam :: acc
                else inst_uparam :: (snd @@ mkFunUnit inst_uparam s) :: acc
      )
    (List.combine3 strpos inst_uparams inst_preds) []
  in
  return @@ Array.of_list inst_sparam

(** Make the [all] predicate for a fresh instance and using [Typing.checked_appvect], given:
    - whether the [all] predicate is the partial one, or the general one [partial_nesting:bool]
    - the positivity of each uniform parameter [bool list]
    - the instantiation of the uniform parameter of the inductive type [constr array]
    - the instation of the fresh predicate [constr option array], using [fun ... => True]
      if the values are none, and [all] is the general predicate
    - the instantiation of the non-uniform parameters and indices
    - the argument to apply it to
*)
let make_all_predicate partial_nesting ref_all strpos inst_uparams inst_preds inst_nuparams_indices arg =
  let* ref_ind = fresh_global ref_all in
  let* inst_uparams = instantiate_all_uparams partial_nesting strpos inst_uparams inst_preds in
  typing_checked_appvect ref_ind @@ Array.concat [inst_uparams; inst_nuparams_indices; [|arg|]]

let mkFuntt x =
  let@ _ = rebind fid Lambda Fresh naming_id x in
  return @@ mkRef ((Rocqlib.lib_ref "core.unit.tt"), EInstance.empty)

let instantiate_all_theorem_uparams partial_nesting strpos inst_uparams preds preds_hold =
  let inst_uparams = Array.to_list inst_uparams in
  let preds = Array.to_list preds in
  let preds_hold = Array.to_list preds_hold in
  let* s = get_state in
  let inst_lfth =
    List.fold_right (fun (positive, inst_uparam, (pred, pred_hold)) acc ->
      if not positive then inst_uparam :: acc else
      match pred, pred_hold with
      | Some pred, Some pred_hold -> inst_uparam :: pred :: pred_hold :: acc
      | None, None ->
        if partial_nesting
        then inst_uparam :: acc
        else inst_uparam :: (snd @@ mkFunUnit inst_uparam s) :: (snd @@ mkFuntt inst_uparam s) :: acc
      | _, _ -> assert false
    )
    (List.combine3 strpos inst_uparams @@ List.combine preds preds_hold) []
  in
  return @@ Array.of_list inst_lfth

(** Make the theorem for the [all] predicate for a fresh instance and using [Typing.checked_appvect], given:
    - whether the [all] predicate is the partial one, or the general one [partial_nesting:bool]
    - the positivity of each uniform parameter [bool list]
    - the instantiation of the uniform parameter of the inductive type [constr array]
    - the instation of the fresh predicate and the proofs they hold [constr option array],
      using [fun ... => True] and [fun _ => I] if the values are none, and [all] is the general predicate
    - the instantiation of the non-uniform parameters and indices
    - the argument to apply it to
*)
let make_all_theorem partial_nesting ref_all_thm strpos inst_uparams inst_preds inst_preds_hold inst_nuparams_indices arg =
  let* ref_ind = fresh_global ref_all_thm in
  let* inst_uparams = instantiate_all_theorem_uparams partial_nesting strpos inst_uparams inst_preds inst_preds_hold in
  typing_checked_appvect ref_ind @@ Array.concat [inst_uparams; inst_nuparams_indices; [|arg|]]


  (** {6 View for Arguments } *)

type head_argument =
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
    as a uniform parameter, the inductive, ainstantiate_all nested argument or a constant. *)
type argument = rel_context * head_argument

(** Decompose the argument in [it_Prod_or_LetIn local, X] where [X] is a uniform parameter, Ind, nested or a constant *)
let view_argument kn mib key_uparams strpos t : argument State.t =
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
    if kn = kn_ind then
      let (_, local_nuparams_indices) = Array.chop mib.mind_nparams_rec iargs in
      let nb_nuparams = mib.mind_nparams - mib.mind_nparams_rec in
      let (local_nuparams, local_indices) = Array.chop nb_nuparams local_nuparams_indices in
      return @@ (cxt, ArgIsInd (pos_ind, local_nuparams, local_indices))
    (* if there is no argument, it cannot be nested *)
    else if Array.length iargs = 0 then return @@ (cxt, ArgIsCst)
    else begin
      (* If it may be nested *)
      let* env = get_env in
      let (mib_nested, ind_nested) = lookup_mind_specif env (kn_ind, pos_ind) in
      let mib_nested_strpos = compute_params_rec_strpos env kn_ind mib_nested in
      (* Check if at least one parameter can be nested upon *)
      if List.exists (fun a -> a) mib_nested_strpos then
        let (inst_uparams, inst_nuparams_indices) = Array.chop mib_nested.mind_nparams_rec iargs in
        return @@ (cxt, ArgIsNested (kn_ind, pos_ind, mib_nested, mib_nested_strpos,
                          ind_nested, inst_uparams, inst_nuparams_indices))
      else
        return @@ (cxt, ArgIsCst)
    end
  | _ -> return @@ (cxt, ArgIsCst)
