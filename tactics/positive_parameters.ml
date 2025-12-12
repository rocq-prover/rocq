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

(************************************************************************)
(************************************************************************)
(* Computes which uniform parameters are strictly positive *)

(* debugging  *)
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
let rec compute_params_rec_strpos_arg compute_params_rec_strpos env kn uparams nparams_rec nparams init_value (arg : constr) : bool list =
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
          let uparams_nested = fst @@ Declareops.split_uparans_nuparams mib_nested.mind_nparams_rec mib_nested.mind_params_ctxt in
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
  let strpos_ctors = andl_array (compute_params_rec_strpos_ctor compute_params_rec_strpos env kn uparams nparams_rec nparams init_value) init_value ctors in
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
  let strpos_inds = andl_array (compute_params_rec_strpos_ind compute_params_rec_strpos env kn uparams nparams_rec nparams init_value) init_value inds in
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
  let (uparams, nuparams) = Declareops.split_uparans_nuparams mib.mind_nparams_rec mib.mind_params_ctxt in
  compute_params_rec_strpos_aux compute_params_rec_strpos env kn uparams nuparams mib.mind_nparams_rec mib.mind_nparams inds
