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
open Names
open EConstr
open Environ
open Evd
open Context
open Util
open Namegen
open Pp

module RelDecl = Rel.Declaration
open RelDecl

(* ************************************************************************** *)
(*                                 State                                      *)
(* ************************************************************************** *)

let _dbg = CDebug.create ~name:"API" ()

type access_key = int (* type of keys *)

(* state *)
module State =
struct

  type state =
    { env : env;
      sigma : evar_map;
      names : Nameops.Fresh.t;
      subst : Esubst.lift;
    }

  type 'a t = state -> 'a

  let return c s = c
  let (let@) x f = x f
  let (let*) x f = fun s -> let a = x s in f a s
  let (let+) x f = fun s -> let (s,a) = x s in f a s

  let get_env s = s.env
  let get_sigma s = s.sigma
  let get_names s = s.names
  let get_state s = s

  (* make functions *)
  let make env sigma = {
    env = env;
    sigma = sigma;
    names = Nameops.Fresh.of_list @@ Termops.ids_of_rel_context @@ rel_context env;
    subst = Esubst.el_id;
  }

  let state_context s = EConstr.of_rel_context @@ Environ.rel_context s.env

  let weaken c s = Vars.exliftn s.subst c

  let weaken_rel c s = RelDecl.map_constr (fun c -> weaken c s) c

  let weaken_context cxt s =
    let nb_cxt = List.length cxt in
    List.mapi (fun i x ->
      let n = nb_cxt - i -1 in
      let weak x = Vars.exliftn (Esubst.el_liftn n s.subst) x in
      match x with
      | LocalAssum (na, ty) -> LocalAssum (na, weak ty)
      | LocalDef (na, bd, ty) -> LocalDef (na, weak bd, weak ty)
      ) cxt

  (* Add variables to the context *)
  let add_names names decl =
    match get_name decl with
    | Anonymous -> names
    | Name id -> Nameops.Fresh.add id names

  let fresh_key s = List.length (state_context s)

  let push_old_rel decl s =
  let s' = { s with
      env = EConstr.push_rel decl s.env ;
      names = add_names s.names decl;
      subst = Esubst.el_lift s.subst;
    } in
  (s', fresh_key s)

  let push_fresh_rel decl s =
    let s' = { s with
      env = EConstr.push_rel decl s.env ;
      names = add_names s.names decl;
      subst = Esubst.el_shft 1 (Esubst.el_lift s.subst);
    } in
  (s', fresh_key s)

  let get_decl key s =
    let n' = List.length (state_context s) - key -1 in
    RelDecl.map_constr (Vars.lift n') (List.nth (state_context s) n')

  let getters f =
    let get_X key s = f (List.length ((state_context s)) - key -1) (get_decl key s) in

    let geti_X keys pos_key s = get_X (List.nth keys pos_key) s in

    let getij_X keyss pos_k1 pos_k2 s = get_X (List.nth (List.nth keyss pos_k1) pos_k2) s in

    let get_Xs keys s = List.map (fun key -> get_X key s) keys in

    (get_X, geti_X, getij_X, get_Xs)

  let get_sdecl_term =
    fun n d ->
    match RelDecl.get_value d with
    | Some tm -> Vars.lift 1 tm
    | None -> mkRel (1+n)

  let get_term, geti_term, getij_term, get_terms = getters get_sdecl_term

  let get_type, geti_type, getij_type, get_types = getters (fun _ d -> Vars.lift 1 (RelDecl.get_type d))

  let get_aname, geti_aname, getij_aname, get_anames = getters (fun _ cdecl -> RelDecl.get_annot cdecl)

  (* Print functions *)
  let print_state print_constr s =
    List.fold_right_i (fun i x acc ->
        acc ++ str "var | " ++ str (string_of_int (List.length (Environ.rel_context s.env) - i)) ++ str " | " ++
        print_constr s.env s.sigma (RelDecl.get_type x)
      ) 0 (state_context s) (str "")

end

open State

(* ************************************************************************** *)
(*                               Naming Schemes                               *)
(* ************************************************************************** *)

type naming_scheme = rel_declaration -> rel_declaration t

(* Keep naming as is, including Anonymous *)
let naming_id decl = return @@ decl

(* Chooses the next Id available from the binder's name.
  If the binder is Anonymous, a name is generated using the head the binder's type. *)
let naming_hd decl =
  let* env = get_env in
  let* sigma = get_sigma in
  let name_or_hd = named_hd env sigma (RelDecl.get_type decl) (RelDecl.get_name decl) in
  return @@ set_name (name_or_hd) decl

let naming_hd_dep dep = if dep then naming_hd else naming_id

let naming_hd_fresh decl =
  let* env = get_env in
  let* sigma = get_sigma in
  let* names = get_names in
  let id = id_of_name_using_hdchar env sigma (RelDecl.get_type decl) (RelDecl.get_name decl) in
  let id = Namegen.mangle_id id in
  let id, avoid = Nameops.Fresh.fresh id names in
  return @@ set_name (Name id) decl

let naming_hd_fresh_dep dep = if dep then naming_hd_fresh else naming_id

(* ************************************************************************** *)
(*                            Fold Functions                                  *)
(* ************************************************************************** *)

(* fold functions for state *)
let fold_right_state f l tp t =
  let rec aux ids1 i l =
    match l with
    | [] -> t (List.rev ids1)
    | a :: l -> tp i a (fun id1 -> aux (f id1 ids1) (i+1) l)
  in
  aux [] 0 l

let fold_left_state f l tp t = fold_right_state f (List.rev l) tp t

let fold_right_state_3 f l tp t =
  let rec aux ids1 ids2 ids3 i l =
    match l with
    | [] -> t (List.rev ids1 , List.rev ids2 , List.rev ids3)
    | a :: l -> tp i a (fun (id1 , id2 , id3) -> aux (f id1 ids1) (f id2 ids2) (f id3 ids3) (i+1) l)
  in
  aux [] [] [] 0 l

let fold_left_state_3 f l tp cc =
  fold_right_state_3 f (List.rev l) tp cc


(* ************************************************************************** *)
(*                            Make Binders                                    *)
(* ************************************************************************** *)

(* Notations to specify functions *)
type freshness = Fresh | Old
type binder = Lambda | Prod

let wrap_binder b =
  match b with
  | Lambda -> mkLambda_or_LetIn
  | Prod -> mkProd_or_LetIn


let add_decl fresh naming_scheme decl cc =
    match fresh with
    | Fresh -> let* name = naming_scheme decl in
               let+ k = push_fresh_rel name in
               cc k
    | Old -> let* decl = weaken_rel decl in
             let* name = naming_scheme decl in
             let+ k = push_old_rel name in
             cc k

(* 1. Keep, and Make Binary Binders and letin *)

let build_binder binder fresh naming_scheme decl cc =
  match fresh with
    | Fresh ->
        let* decl = naming_scheme decl in
        let+ k = push_fresh_rel decl in
        let* v = cc k in
        return @@ wrap_binder binder decl v
    | Old ->
        let* decl = weaken_rel decl  in
        let* decl = naming_scheme decl in
        let+ k = push_old_rel decl in
        let* v = cc k in
        return @@ wrap_binder binder decl v

let make_binder binder naming_scheme na ty = build_binder binder Fresh naming_scheme (LocalAssum (na, ty))
let keep_binder binder naming_scheme na ty = build_binder binder Old naming_scheme (LocalAssum (na, ty))

let build_binder_opt binder fresh naming_scheme decl cc =
  match fresh with
    | Fresh ->
        let* decl = naming_scheme decl in
        let+ k = push_fresh_rel decl in
        let* v = cc k in
        return @@ Option.map (wrap_binder binder decl) v
    | Old ->
        let* decl = weaken_rel decl  in
        let* decl = naming_scheme decl in
        let+ k = push_old_rel decl in
        let* v = cc k in
        return @@ Option.map (wrap_binder binder decl) v

let make_binder_opt binder naming_scheme na ty = build_binder_opt binder Fresh naming_scheme (LocalAssum (na, ty))
let keep_binder_opt binder naming_scheme na ty = build_binder_opt binder Old naming_scheme (LocalAssum (na, ty))

(* 2. Iterate binders *)
let read_context binder cxt = fold_left_state (fun a l -> a :: l) cxt (fun _ -> binder)

let add_context fresh naming_scheme = read_context (add_decl fresh naming_scheme)
let closure_context binder fresh naming_scheme = read_context (build_binder binder fresh naming_scheme)

let closure_context_opt binder fresh naming_scheme = read_context (build_binder_opt binder fresh naming_scheme)

(* seperate var and letin in key_vars / key_letins / key_both *)

let read_context_sep binder cxt =
  fold_left_state_3 List.append cxt (fun _ decl cc ->
    let@ key = binder decl in
    match decl with
    | LocalAssum _ -> cc ([key],[],[key])
    | LocalDef _   -> cc ([],[key],[key])
  )

let add_context_sep fresh naming_scheme = read_context_sep (add_decl fresh naming_scheme)
let closure_context_sep binder fresh naming_scheme = read_context_sep (build_binder binder fresh naming_scheme)
let closure_context_sep_opt binder fresh naming_scheme = read_context_sep (build_binder_opt binder fresh naming_scheme)

(* takes a continuation after binder var and letin to add fresh binders and decide what to do with the keys *)
let read_by_decl cxt binder cc_letin cc_var =
  fold_left_state List.append cxt (fun pos_decl decl cc ->
    let@ key = binder decl in
    match decl with
    | LocalDef _   -> cc_letin pos_decl key cc
    | LocalAssum _ -> cc_var   pos_decl key cc
  )

(* ************************************************************************** *)
(*                           Functions on Inductive                           *)
(* ************************************************************************** *)

let get_args mdecl u (cxt, ty) =
  let nb_params_letin = List.length mdecl.mind_params_ctxt in
  let (_, args) = List.chop nb_params_letin (List.rev cxt) in
  let args = Vars.subst_instance_context u @@ EConstr.of_rel_context @@ List.rev args in
  let* sigma = get_sigma in
  let (hd, xs) = decompose_app sigma (Vars.subst_instance_constr u @@ EConstr.of_constr ty) in
  let indices = Array.sub xs mdecl.mind_nparams (Array.length xs - mdecl.mind_nparams) in
  return (args, indices)

let iterate_ctors mdecl ind u tp cc =
  let* state = get_state in
  let f a = get_args mdecl u a state in
  let ctors = Array.to_list @@ Array.map f ind.mind_nf_lc in
  fold_right_state (fun a l -> a :: l) ctors tp cc

let make_ind ((kn, pos_ind), u) key_uparams key_nuparams key_indices =
  let tInd = mkIndU ((kn, pos_ind), u) in
  let* args = get_terms (key_uparams @ key_nuparams @ key_indices) in
  let args = Array.of_list args in
  return @@ mkApp (tInd, args)

let make_cst ((kn, pos_ind), u) pos_ctor key_uparams key_nuparams args =
  let tCst = mkConstructU (((kn, pos_ind), 1+pos_ctor), u) in
  let* termu = get_terms key_uparams in
  let* termnu = get_terms key_nuparams in
  return @@ mkApp (tCst, (Array.of_list (termu @ termnu @ args)))

(* make fix *)
let make_fix ind_bodies focus fix_rarg fix_name fix_type tmc =
  (* data fix *)
  let rargs = List.mapi fix_rarg ind_bodies in
  let fix_names = List.mapi fix_name ind_bodies in
  let* state = get_state in
  let fix_type a b = fix_type a b state in
  let fix_types = List.mapi fix_type ind_bodies in
  (* update context continuation *)
  let fix_context = List.rev @@ List.map2_i (fun i na ty -> LocalAssum (na, Vars.lift i ty)) 0 fix_names fix_types in
  let@ key_Fix = add_context Fresh naming_id fix_context in
  let* state = get_state in
  let tmc a = tmc a state in
  let fix_bodies = List.mapi (fun pos_list ind -> tmc (key_Fix, pos_list, ind)) ind_bodies in
  (* result *)
  return @@ EConstr.mkFix ((Array.of_list rargs, focus), (Array.of_list fix_names, Array.of_list fix_types, Array.of_list fix_bodies))

let get_indices indb u =
  let indices, _ = List.chop indb.mind_nrealdecls indb.mind_arity_ctxt in
  weaken_context (Vars.subst_instance_context u (EConstr.of_rel_context indices))

(* make match *)
let make_case_or_projections naming_vars mdecl ind indb u key_uparams key_nuparams params indices mk_case_pred case_relevance tm_match tc =
  let* env = get_env in
  let case_info = Inductiveops.make_case_info env ind RegularStyle in
  let case_invert =
    if Typeops.should_invert_case env (Unsafe.to_relevance case_relevance) case_info
    then Constr.CaseInvert {indices=Array.of_list indices}
    else Constr.NoInvert
  in

  let case_pred =
    (* indices *)
    let* i = get_indices indb u in
    let@ key_fresh_indices, _ , key_both = add_context_sep Fresh naming_vars i in
    (* new var *)
    let* t = get_terms (key_uparams @ key_nuparams @ key_fresh_indices) in
    let ty_var = mkApp (mkIndU (ind, u), Array.of_list t) in
    let* env = get_env in
    let name_var_match = make_annot Anonymous (Inductiveops.relevance_of_inductive env (ind, u)) in
    let@ key_var_match = add_decl Fresh naming_vars (LocalAssum (name_var_match, ty_var)) in
    (* return type *)
    let* name = get_anames (key_both @ [key_var_match]) in
    let fresh_annot = Array.of_list name in
    let* return_type = mk_case_pred key_fresh_indices key_var_match in
    return @@ ((fresh_annot, return_type), case_relevance)
  in
  let branch pos_ctor ctor =
    let* args = get_args mdecl u ctor in
    let args = fst args in
    let@ key_args, key_letin , key_both = add_context_sep Old naming_vars args in
    let* branches_body = tc (key_args, key_letin, key_both, pos_ctor) in
    let* name = get_anames key_both in
    let names_args = Array.of_list name in
    return (names_args, branches_body)
  in

  let branches = let* state = get_state in
                 let branch a b = branch a b state in
                 return @@ Array.mapi branch indb.mind_nf_lc in

  let* branches, pred =
    let* env = get_env in
    let* sigma = get_sigma in
    let* case_pred, r = case_pred in
    let* branches = branches in
    let branches, case_pred = EConstr.case_expand env (case_info.ci_ind, u) params case_pred branches in
    return (branches, (case_pred, r)) in

  let* env = get_env in
  let* sigma = get_sigma in
  return @@ Inductiveops.simple_make_case_or_project env sigma case_info pred case_invert tm_match branches
