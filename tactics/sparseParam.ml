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


  (** {6 Lookup Sparse Parametricity } *)

let warn_no_sparse_parametricity =
  CWarnings.create ~name:"no-sparse-parametricity" ~category:Deprecation.Version.v9_2
  Pp.(fun (ind, ind_nested) ->
    Nametab.XRefs.pr (TrueGlobal (IndRef ind)) ++ str " is nested using " ++
    Nametab.XRefs.pr (TrueGlobal (IndRef ind_nested)) ++ str " but sparse parametricity for " ++
    Nametab.XRefs.pr (TrueGlobal (IndRef ind_nested)) ++ str " is not registered.\n"
    )

let warn_no_local_fundamental_theorem =
  CWarnings.create ~name:"no-local_fundamental_theorem" ~category:Deprecation.Version.v9_2
  Pp.(fun (ind,ind_nested) ->
    Nametab.XRefs.pr (TrueGlobal (IndRef ind)) ++ str " is nested using " ++
    Nametab.XRefs.pr (TrueGlobal (IndRef ind_nested)) ++ str " but the local fundamental theorem for " ++
    Nametab.XRefs.pr (TrueGlobal (IndRef ind_nested)) ++ str " is not registered.\n"
    )

let lookup_sparse_parametricity ind ind_nested =
  match DeclareScheme.lookup_scheme_opt "sparse_parametricity" ind_nested with
  | None -> warn_no_sparse_parametricity (ind, ind_nested); None
  | Some ref_sparam ->
  match DeclareScheme.lookup_scheme_opt "local_fundamental_theorem" ind_nested with
  | None -> warn_no_local_fundamental_theorem (ind, ind_nested); None
  | Some ref_lfth -> Some (ref_sparam, ref_lfth)


  (** {6 Instantiate Sparse Parametricity } *)

open EConstr
open Inductive
open LibBinding
open State

let (let@) x f = x f
let (let*) x f = State.bind x f

let mkFunTrue x =
  let@ _ = rebind fid Lambda Fresh naming_id x in
  return @@ mkRef ((Rocqlib.lib_ref "core.True.type"), EInstance.empty)

let instantiate_sparse_parametricity inst_uparams strpos preds =
  let preds = Array.to_list preds in
  let inst_uparams = Array.to_list inst_uparams in
  let* s = get_state in
  let inst_sparam =
    List.fold_right (fun (inst_uparam, b, pred) acc ->
      if not b then inst_uparam :: acc else
      match pred with
      | None -> inst_uparam :: (snd @@ mkFunTrue inst_uparam s) :: acc
      | Some pred -> inst_uparam :: pred :: acc
      )
    (List.combine3 inst_uparams strpos preds) []
  in
  return @@ Array.of_list inst_sparam

let mkFunI x =
  let@ _ = rebind fid Lambda Fresh naming_id x in
  return @@ mkRef ((Rocqlib.lib_ref "core.True.I"), EInstance.empty)

let instantiate_fundamental_theorem inst_uparams strpos preds preds_hold =
  let inst_uparams = Array.to_list inst_uparams in
  let preds = Array.to_list preds in
  let preds_hold = Array.to_list preds_hold in
  let* s = get_state in
  let inst_lfth =
    List.fold_right (fun (inst_uparam, b, (pred, pred_hold)) acc ->
      if not b then inst_uparam :: acc else
      match pred, pred_hold with
      | None, None -> inst_uparam :: (snd @@ mkFunTrue inst_uparam s) :: (snd @@ mkFunI inst_uparam s) :: acc
      | Some pred, Some pred_hold -> inst_uparam :: pred :: pred_hold :: acc
      | _, _ -> assert false
    )
    (List.combine3 inst_uparams strpos @@ List.combine preds preds_hold) []
  in
  return @@ Array.of_list inst_lfth


  (** {6 View for Arguments } *)

type head_arg =
  (* pos_ind, constant context, inst_nuparams inst_indices *)
  | ArgIsInd of int * constr array * constr array
  (** get the position in ind_bodies out of the position of mind_packets *)
  (* kn_nested, pos_nested, inst_uparams, inst_nuparams_indices *)
  | ArgIsNested of MutInd.t * int
                   * mutual_inductive_body * bool list * one_inductive_body
                  * constr array * constr array
  (* constant context, hd, args (maybe empty) *)
  | ArgIsCst

(** View to decompose arguments as [forall locs, X] where [X] is further decomposed
    as a uniform parameter, the inductive, a nested argument or a constant. *)
type arg = rel_context * head_arg

(* Decompose the argument in [it_Prod_or_LetIn local, X] where [X] is Ind, nested or a constant *)
let view_arg kn mib t : arg State.t =
  let* (cxt, hd) = whd_decompose_prod_decls t in
  let* (hd, iargs) = decompose_app hd in
  let* sigma = get_sigma in
  match kind sigma hd with
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
      let mib_nested_strpos = compute_params_rec_strpos env kn_ind mib_nested in
      (* Check if at least one parameter can be nested upon *)
      if List.exists (fun a -> a) mib_nested_strpos then
        let (inst_uparams, inst_nuparams_indices) = Array.chop mib_nested.mind_nparams_rec iargs in
        return @@ (cxt, ArgIsNested (kn_ind, pos_ind, mib_nested, mib_nested_strpos,
                          ind_nested, inst_uparams, inst_nuparams_indices))
      else return @@ (cxt, ArgIsCst)
    end
  | _ -> return @@ (cxt, ArgIsCst)
