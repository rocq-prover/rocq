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

module RelDecl = Rel.Declaration
open RelDecl

(* ************************************************************************** *)
(*                                 State                                      *)
(* ************************************************************************** *)

let _dbg = CDebug.create ~name:"API" ()

(* state *)
module State =
struct

  (* Monad *)
  type state =
    { env : env;
      names : Nameops.Fresh.t;
      subst : Esubst.lift;
    }

  type 'a t = state -> evar_map -> evar_map * 'a

  let return c = fun _ sigma -> (sigma, c)
  let bind x f = fun s sigma -> let (sigma, a) = x s sigma in f a s sigma
  let map f t = bind t (fun a -> return @@ f a)
  let run_state s sigma t = t s sigma
  let run env sigma t =
      let s = {
      env = env;
      names = Nameops.Fresh.of_list @@ Termops.ids_of_rel_context @@ rel_context env;
      subst = Esubst.el_id;
    }
  in t s sigma

  (* Notation for the monad *)
  let (let@) x f = x f
  let (let*) x f = bind x f

  (* Access the current state *)
  let get_env = fun s -> return s.env s
  let get_sigma = fun s sigma -> return sigma s sigma
  let get_names = fun s -> return s.names s
  let get_state = fun s -> return s s
  let get_context = fun s -> return (EConstr.of_rel_context @@ Environ.rel_context s.env) s


(** {6 Weaken Functions From the Former Context to the New Context } *)

  let weaken c = fun s -> return (Vars.exliftn s.subst c) s

  let weaken_rel decl =
    fun s sigma -> return (RelDecl.map_constr (fun t -> snd @@ weaken t s sigma) decl) s sigma

  let weaken_context cxt s sigma =
    let nb_cxt = List.length cxt in
    let wcxt = List.mapi (fun i x ->
      let n = nb_cxt - i -1 in
      let weak x = Vars.exliftn (Esubst.el_liftn n s.subst) x in
      match x with
      | LocalAssum (na, ty) -> LocalAssum (na, weak ty)
      | LocalDef (na, bd, ty) -> LocalDef (na, weak bd, weak ty)
      ) cxt
    in
    return wcxt s sigma

(** {6 Access Key } *)

  type access_key = int

  let fresh_key s =
    let (_, ctx) = get_context s Evar_empty in
    List.length ctx

  let make_key i =
    let* ctx = get_context in
    return @@ List.length ctx - i

(** {6 Push Functions } *)

  (* Add variables to the context *)
  let add_names names decl =
    match get_name decl with
    | Anonymous -> names
    | Name id -> Nameops.Fresh.add id names

  let push_old_rel decl s sigma =
  let s' = {
      env = EConstr.push_rel decl s.env ;
      names = add_names s.names decl;
      subst = Esubst.el_lift s.subst;
    } in
  return (s', fresh_key s) s' sigma

  let push_fresh_rel decl s sigma =
    let s' = {
      env = EConstr.push_rel decl s.env ;
      names = add_names s.names decl;
      subst = Esubst.el_shft 1 (Esubst.el_lift s.subst);
    } in
  return (s', fresh_key s) s' sigma


(** {6 Access Functions } *)

  let get_decl key =
    let* ctx = get_context in
    let n' = List.length ctx - key -1 in
    let decl = RelDecl.map_constr (Vars.lift n') (List.nth ctx n') in
    return decl

  let getters f =
    let get_X key =
      let* decl = get_decl key in
      let* cxt = get_context in
      return (f (List.length cxt - key -1) decl) in

    let geti_X keys pos_key = get_X (List.nth keys pos_key) in

    let getij_X keyss pos_k1 pos_k2 = get_X (List.nth (List.nth keyss pos_k1) pos_k2) in

    let get_Xs keys =
      fun s sigma ->
      return (Array.of_list @@ List.map (fun key -> snd @@ get_X key s sigma) keys) s sigma in

    (get_X, geti_X, getij_X, get_Xs)

  let get_sdecl_term =
    fun n d ->
    match RelDecl.get_value d with
    | Some tm -> Vars.lift 1 tm
    | None -> mkRel (1+n)

  let get_term, geti_term, getij_term, get_terms = getters get_sdecl_term

  let get_type, geti_type, getij_type, get_types = getters (fun _ d -> Vars.lift 1 (RelDecl.get_type d))

  let get_aname, geti_aname, getij_aname, get_anames = getters (fun _ cdecl -> RelDecl.get_annot cdecl)

  let index0_opt_i p l =
      let rec aux i l = match l with
      | [] -> None
      | h::_ when p i h -> Some (i, h)
      | _::t -> aux (1+i) t
      in aux 0 l

  let check_key_in k keys =
    let* k = make_key k in
    return @@ Option.map fst @@ index0_opt_i (fun _ key -> k = key) keys

(** {6 Access Functions } *)

  let list_mapi f l =
    let rec aux i l acc s sigma =
      match l with
      | [] -> (sigma, acc)
      | a::l -> let (sigma, t) = (f i a) s sigma in
                aux (i + 1) l (t::acc) s sigma
    in
  let* acc = aux 0 l [] in
  return @@ List.rev acc

  let list_map2i f la lb =
    let rec aux i la lb acc s sigma =
      match la, lb with
      | [], [] -> (sigma, acc)
      | a::la, b::lb -> let (sigma, t) = (f i a b) s sigma in
                aux (i + 1) la lb (t::acc) s sigma
      | _,_ -> assert false
    in
  let* acc = aux 0 la lb [] in
  return @@ List.rev acc

  let array_mapi f ar =
    fun s sigma ->
    let sigma_ref = ref sigma in
    let size_ar = Array.length ar in
    if size_ar = 0 then
      (!sigma_ref, [||])
    else begin
      let update_pos i =
        let (sigma, x) = f i ar.(i) s !sigma_ref in
        sigma_ref := sigma;
        x
      in
      let r = Array.init size_ar update_pos in
      (!sigma_ref, r)
    end

  let array_map2i f ar1 ar2 =
    fun s sigma ->
    let sigma_ref = ref sigma in
    let size_ar = Array.length ar1 in
    if size_ar = 0
    then (!sigma_ref, [||])
    else begin
      let update_pos i =
        let (sigma, x) = f i ar1.(i) ar2.(i) s !sigma_ref in
        sigma_ref := sigma;
        x
      in
      let r = Array.init size_ar update_pos in
      (!sigma_ref, r)
    end

end

open State

(* ************************************************************************** *)
(*                               Naming Schemes                               *)
(* ************************************************************************** *)

let name_hd decl =
  let* env = get_env in
  let* sigma = get_sigma in
  return @@ named_hd env sigma (RelDecl.get_type decl) (RelDecl.get_name decl)

type naming_scheme = rel_declaration -> rel_declaration t

(* Keep naming as is, including Anonymous *)
let naming_id decl = return decl

(* Chooses the next Id available from the binder's name.
  If the binder is Anonymous, a name is generated using the head the binder's type. *)
let naming_hd decl =
  let* name_or_hd = name_hd decl in
  return @@ set_name name_or_hd decl

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
(*                             Operations                                     *)
(* ************************************************************************** *)

let ind_relevance ind u =
  let* sigma = get_sigma in
  return @@ ERelevance.make @@ Inductive.relevance_of_ind_body ind (EInstance.kind sigma u)

(* Decompose and Manipulate Terms *)
let whd_decompose_prod_decls t =
  let* env = get_env in
  let* sigma = get_sigma in
  return @@ Reductionops.whd_decompose_prod_decls env sigma t

let decompose_lambda_decls t =
  let* sigma = get_sigma in
  return @@ decompose_lambda_decls sigma t

let decompose_app t =
  let* sigma = get_sigma in
  return @@ decompose_app sigma t

let eta_expand_instantiation inst ctxt =
  let* env = get_env in
  let* sigma = get_sigma in
  return @@ Reductionops.eta_expand_instantiation env sigma inst ctxt

let fresh_global ref =
  fun s sigma ->
  let (sigma, t) = fresh_global s.env sigma ref in
  return t s sigma

let fresh_inductive_instance ind =
  fun s sigma ->
  let sigma, ((_, u)) = Evd.fresh_inductive_instance s.env sigma ind in
  return u s sigma

let fresh_sort_ql ?sort_rigid ?name r =
  fun s sigma ->
  let sigma, q, u = Evd.new_sort_info ?sort_rigid ?name r sigma in
  return (q,u) s sigma

let new_univ_level_variable ?name r =
  fun s sigma ->
  let (sigma, l) = Evd.new_univ_level_variable ?name r sigma in
  return l s sigma

(* Typing and Retyping *)
let typing_checked_appvect f xs s sigma =
  let (sigma, t) = Typing.checked_appvect s.env sigma f xs in
  return t s sigma

let typing_check_actual_type jud ty : unit t =
  fun s sigma ->
  let sigma = Typing.check_actual_type s.env sigma jud ty in
  return () s sigma

let retyping_sort_of t =
  let* env = get_env in
  let* sigma = get_sigma in
  return @@ Retyping.get_sort_of env sigma t

let retyping_judgment_of tm =
  let* env = get_env in
  let* sigma = get_sigma in
  return @@ Retyping.get_judgment_of env sigma tm

(* debug *)
let print_term dbg s t =
  let* env = get_env in
  let* sigma = get_sigma in
  return @@ dbg Pp.(fun () -> str s ++ Termops.Internal.print_constr_env env sigma t)

let print_current_context dbg s =
  let* env = get_env in
  let* sigma = get_sigma in
  return @@ dbg Pp.(fun () -> str s ++ Termops.Internal.print_rel_context env sigma)


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

let wrap_decl map f fresh naming_scheme decl cc s sigma =
  match fresh with
    | Fresh ->
        let (sigma, decl) = naming_scheme decl s sigma in
        let (sigma, (s', k)) = push_fresh_rel decl s sigma in
        let (sigma, v) = cc k s' sigma in
        return (map (f decl) v) s sigma
    | Old ->
        let (sigma, decl) = weaken_rel decl s sigma in
        let (sigma, decl) = naming_scheme decl s sigma in
        let (sigma, (s', k)) = push_old_rel decl s sigma in
        let (sigma, v) = cc k s' sigma in
        return (map (f decl) v) s sigma

let fid f x = f x
let fright f (a,b) = (a, f b)
let fleft f (a,b) = (f a, b)
let fopt = Option.map
let fropt = fun f -> Option.map (fun (a,b) -> (a, f b))

let add_decl a = wrap_decl fid (fun _ x -> x) a

let build_binder m binder = wrap_decl m (wrap_binder binder)
let make_binder m binder naming_scheme na ty = build_binder m binder Fresh naming_scheme (LocalAssum (na, ty))
let keep_binder m binder naming_scheme na ty = build_binder m binder Old naming_scheme (LocalAssum (na, ty))

(* 2. Iterate binders *)

(* seperate var and letin in key_vars / key_letins / key_both *)
let read_context_sep binder cxt =
  fold_left_state_3 List.append cxt (fun _ decl cc ->
    let@ key = binder decl in
    match decl with
    | LocalAssum _ -> cc ([key],[],[key])
    | LocalDef _   -> cc ([],[key],[key])
  )

let read_context_sep_forget binder cxt cc =
  read_context_sep binder cxt (fun (x,_,_) -> cc x)

let add_context fresh naming_scheme = read_context_sep_forget (add_decl fresh naming_scheme)
let add_context_sep fresh naming_scheme = read_context_sep (add_decl fresh naming_scheme)

let closure_context m binder fresh naming_scheme = read_context_sep_forget (build_binder m binder fresh naming_scheme)
let closure_context_sep m binder fresh naming_scheme = read_context_sep (build_binder m binder fresh naming_scheme)

let rebind m binder freshness naming_scheme ty cc =
  (* decompose type, and rebind local variable *)
  let* (locs, hd) =
    match binder with
    | Prod ->  whd_decompose_prod_decls ty
    | Lambda -> decompose_lambda_decls ty
  in
  let@ key_locs = closure_context m binder freshness naming_scheme locs in
  (* rebind the head *)
  let* sort = retyping_sort_of hd in
  let rev_hd = ESorts.relevance_of_sort sort in
  let name_hd = make_annot Anonymous rev_hd in
  let@ key_hd = build_binder m binder freshness naming_scheme @@ LocalAssum (name_hd, hd) in
  (* continuation *)
  cc (key_locs, key_hd)

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

let get_args mib u (cxt, ty) =
  let nb_params_letin = List.length mib.mind_params_ctxt in
  let (_, args) = List.chop nb_params_letin (List.rev cxt) in
  let args = Vars.subst_instance_context u @@ EConstr.of_rel_context @@ List.rev args in
  let* (hd, xs) = decompose_app (Vars.subst_instance_constr u @@ EConstr.of_constr ty) in
  let indices = Array.sub xs mib.mind_nparams (Array.length xs - mib.mind_nparams) in
  return (args, indices)

let iterate_ctors mib ind u tp cc =
  let* ctors = array_mapi (fun _ -> get_args mib u) ind.mind_nf_lc in
  fold_right_state (fun a l -> a :: l) (Array.to_list ctors) tp cc

let make_ind ((kn, pos_ind), u) key_uparams key_nuparams key_indices =
  let tInd = mkIndU ((kn, pos_ind), u) in
  let* inst_ind = get_terms (key_uparams @ key_nuparams @ key_indices) in
  return @@ mkApp (tInd, inst_ind)

let make_cst ((kn, pos_ind), u) pos_ctor key_uparams key_nuparams args =
  let tCst = mkConstructU (((kn, pos_ind), 1+pos_ctor), u) in
  let* params = get_terms (key_uparams @ key_nuparams) in
  return @@ mkApp (tCst, (Array.concat [params; args]))

(* make fix *)
let make_fix ind_bodies focus fix_rarg fix_name fix_type tmc =
  (* data fix *)
  let rargs = List.mapi fix_rarg ind_bodies in
  let fix_names = List.mapi fix_name ind_bodies in
  let* fix_types = list_mapi fix_type ind_bodies in
  (* update context continuation *)
  let fix_context = List.rev @@ List.map2_i (fun i na ty -> LocalAssum (na, Vars.lift i ty)) 0 fix_names fix_types in
  let@ key_Fix = add_context Fresh naming_id fix_context in
  let* fix_bodies = list_mapi (fun pos_list ind -> tmc (key_Fix, pos_list, ind)) ind_bodies in
  (* result *)
  return @@ EConstr.mkFix ((Array.of_list rargs, focus), (Array.of_list fix_names, Array.of_list fix_types, Array.of_list fix_bodies))

let get_indices indb u =
  let indices, _ = List.chop indb.mind_nrealdecls indb.mind_arity_ctxt in
  weaken_context (Vars.subst_instance_context u (EConstr.of_rel_context indices))

(* make match *)
let make_case_or_projections naming_vars mib ind indb u key_uparams key_nuparams params indices mk_case_pred case_relevance tm_match tc =
  let* env = get_env in
  let* sigma = get_sigma in
  let case_info = Inductiveops.make_case_info env ind MatchStyle in

  let case_invert =
    if Inductiveops.Internal.should_invert_case env sigma (ERelevance.kind sigma case_relevance) case_info
    then Constr.CaseInvert {indices=indices}
    else Constr.NoInvert
  in

  let case_pred =
    (* indices *)
    let* indices = get_indices indb u in
    let@ key_fresh_indices, _ , key_both = add_context_sep Fresh naming_vars indices in
    (* new var *)
    let* inst_ind = get_terms (key_uparams @ key_nuparams @ key_fresh_indices) in
    let ty_var = mkApp (mkIndU (ind, u), inst_ind) in
    let* env = get_env in
    let name_var_match = make_annot Anonymous (Inductiveops.relevance_of_inductive env (ind, u)) in
    let@ key_var_match = add_decl Fresh naming_vars (LocalAssum (name_var_match, ty_var)) in
    (* return type *)
    let* fresh_annot = get_anames (key_both @ [key_var_match]) in
    let* return_type = mk_case_pred key_fresh_indices key_var_match in
    return @@ ((fresh_annot, return_type), case_relevance)
  in

  let branch pos_ctor ctor =
    let* args = get_args mib u ctor in
    let args = fst args in
    let@ key_args, key_letin, key_both = add_context_sep Old naming_vars args in
    let* branches_body = tc (key_args, key_letin, key_both, pos_ctor) in
    let* names_args = get_anames key_both in
    return (names_args, branches_body)
  in

  let* case_info, pred, case_invert, c, branches =
    let* case_pred = case_pred in
    let* branches = array_mapi branch indb.mind_nf_lc in
    let* env = get_env in
    let* sigma = get_sigma in
    return @@ EConstr.expand_case env sigma (case_info, u, params, case_pred, case_invert, tm_match, branches)
  in

  let* env = get_env in
  let* sigma = get_sigma in
  return @@ Inductiveops.simple_make_case_or_project env sigma case_info pred case_invert c branches
