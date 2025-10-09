(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*i*)
open Names
open Constr
open Evd
open Util
open Typeclasses_errors

(*i*)

(* Core typeclasses hints *)
type 'a hint_info_gen =
    { hint_priority : int option;
      hint_pattern : 'a option }

type hint_info = (Id.Set.t * Pattern.constr_pattern) hint_info_gen

let { Goptions.get = get_typeclasses_unique_solutions } =
  Goptions.declare_bool_option_and_ref
    ~key:["Typeclasses";"Unique";"Solutions"]
    ~value:false
    ()

type class_method = {
  meth_name : Name.t;
  meth_const : Constant.t option;
}

(* This module defines type-classes *)
type typeclass = {
  (* Universe quantification *)
  cl_univs : UVars.AbstractContext.t;

  (* The class implementation *)
  cl_impl : GlobRef.t;

  cl_context : Constr.rel_context;

  cl_trivial : bool;

  cl_props : Constr.rel_context;

  cl_projs : class_method list;

  cl_strict : bool;

  cl_unique : bool;
}

module GlobRefMap = Environ.QGlobRef.Map

type typeclasses = typeclass GlobRefMap.t
(* Invariant: for any pair (gr, tc) in the map, gr and tc.cl_impl are equal *)

type instance = {
  is_class: GlobRef.t;
  is_info: hint_info;
  is_impl: GlobRef.t;
}

type instances = (instance GlobRefMap.t) GlobRefMap.t

let instance_impl is = is.is_impl

let hint_priority is = is.is_info.hint_priority

(*
 * states management
 *)

let classes : typeclasses CRef.ref = Summary.ref GlobRefMap.empty ~name:"classes"
let instances : instances CRef.ref = Summary.ref GlobRefMap.empty ~name:"instances"

let class_info env c = GlobRefMap.find_opt env c CRef.(!classes)

let class_info_exn env sigma r =
  match class_info env r with
  | Some v -> v
  | None ->
    let sigma, c = Evd.fresh_global env sigma r in
    not_a_class env sigma c

let global_class_of_constr env sigma c =
  try let gr, u = EConstr.destRef sigma c in
    GlobRefMap.find env gr CRef.(!classes), u
  with DestKO | Not_found -> not_a_class env sigma c

let decompose_class_app env sigma c =
  let hd, args = EConstr.decompose_app_list sigma c in
  match EConstr.kind sigma hd with
  | Proj (p, _, c) ->
    let expp = Retyping.expand_projection env sigma p c args in
    EConstr.decompose_app_list sigma expp
  | _ -> hd, args

let dest_class_app env sigma c =
  let cl, args = decompose_class_app env sigma c in
    global_class_of_constr env sigma cl, (List.map EConstr.Unsafe.to_constr args)

let dest_class_arity env sigma c =
  let open EConstr in
  let rels, c = decompose_prod_decls sigma c in
    rels, dest_class_app (push_rel_context rels env) sigma c

let class_of_constr env sigma c =
  try Some (dest_class_arity env sigma c)
  with e when CErrors.noncritical e -> None

let is_class_constr env sigma c =
  try let gr, u = EConstr.destRef sigma c in
    GlobRefMap.mem env gr CRef.(!classes)
  with DestKO | Not_found -> false

let rec is_class_type env evd c =
  let c, _ = EConstr.decompose_app evd c in
    match EConstr.kind evd c with
    | Prod (_, _, t) -> is_class_type env evd t
    | Cast (t, _, _) -> is_class_type env evd t
    | Proj (p, _, c) -> GlobRefMap.mem env (GlobRef.ConstRef (Projection.constant p)) CRef.(!classes)
    | _ -> is_class_constr env evd c

let is_class_evar env evd evi =
  is_class_type env evd (Evd.evar_concl evi)

let rec is_maybe_class_type env evd c =
  let c, _ = EConstr.decompose_app evd c in
    match EConstr.kind evd c with
    | Prod (_, _, t) -> is_maybe_class_type env evd t
    | Cast (t, _, _) -> is_maybe_class_type env evd t
    | Evar _ -> true
    | Proj (p, _, c) -> GlobRefMap.mem env (GlobRef.ConstRef (Projection.constant p)) CRef.(!classes)
    | _ -> is_class_constr env evd c

let load_class env cl =
  CRef.(classes := GlobRefMap.add env cl.cl_impl cl !classes)

(** Build the subinstances hints. *)

(*
 * interface functions
 *)

let load_instance env inst =
  let open CRef in
  let insts =
    try GlobRefMap.find env inst.is_class !instances
    with Not_found -> GlobRefMap.empty in
  let insts = GlobRefMap.add env inst.is_impl inst insts in
  instances := GlobRefMap.add env inst.is_class insts !instances

let remove_instance env inst =
  let open CRef in
  let insts =
    try GlobRefMap.find env inst.is_class !instances
    with Not_found -> assert false in
  let insts = GlobRefMap.remove env inst.is_impl insts in
  instances := GlobRefMap.add env inst.is_class insts !instances

let typeclasses () = GlobRefMap.fold (fun _ l c -> l :: c) CRef.(!classes) []

let cmap_elements c = GlobRefMap.fold (fun k v acc -> v :: acc) c []

let instances_of env c =
  try cmap_elements (GlobRefMap.find env c.cl_impl CRef.(!instances)) with Not_found -> []

let all_instances () =
  GlobRefMap.fold (fun k v acc ->
    GlobRefMap.fold (fun k v acc -> v :: acc) v acc)
    CRef.(!instances) []

let instances env r =
  Option.map (fun m -> instances_of env m) (class_info env r)

let instances_exn env sigma r =
  match instances env r with
  | Some v -> v
  | None ->
    let sigma, c = Evd.fresh_global env sigma r in
    not_a_class env sigma c

let is_class env gr =
  GlobRefMap.mem env gr CRef.(!classes)

open Evar_kinds
type evar_filter = Evar.t -> Evar_kinds.t Lazy.t -> bool

let make_unresolvables filter evd =
  let tcs = Evd.get_typeclass_evars evd in
  Evd.set_typeclass_evars evd (Evar.Set.filter (fun x -> not (filter x)) tcs)

let all_evars _ _ = true
let all_goals _ source =
  match Lazy.force source with
  | VarInstance _ | GoalEvar -> true
  | _ -> false

let no_goals ev evi = not (all_goals ev evi)
let no_goals_or_obligations _ source =
  match Lazy.force source with
  | VarInstance _ | GoalEvar | QuestionMark _ -> false
  | _ -> true

let has_typeclasses filter evd =
  let tcs = get_typeclass_evars evd in
  let check ev = filter ev (lazy (snd (Evd.evar_source (Evd.find_undefined evd ev)))) in
  Evar.Set.exists check tcs

let get_filtered_typeclass_evars filter evd =
  let tcs = get_typeclass_evars evd in
  let check ev = filter ev (lazy (snd (Evd.evar_source (Evd.find_undefined evd ev)))) in
  Evar.Set.filter check tcs

let solve_all_instances_hook = CRef.ref (fun env evd filter unique fail -> assert false)

let solve_all_instances env evd filter unique fail =
  let open CRef in
  !solve_all_instances_hook env evd filter unique fail

let set_solve_all_instances f = CRef.(solve_all_instances_hook := f)

let resolve_typeclasses ?(filter=no_goals) ?(unique=get_typeclasses_unique_solutions ())
    ?(fail=true) env evd =
  if not (has_typeclasses filter evd) then evd
  else solve_all_instances env evd filter unique fail

(** In case of unsatisfiable constraints, build a nice error message *)

let error_unresolvable env evd comp =
  let exception MultipleFound in
  let fold ev accu =
    match Evd.find_undefined evd ev with
    | exception Not_found -> None
    | evi ->
      let ev_class = class_of_constr env evd (Evd.evar_concl evi) in
      if Option.is_empty ev_class then accu
      else (* focus on one instance if only one was searched for *)
      if Option.has_some accu then raise MultipleFound
      else (Some ev)
  in
  let ev = try Evar.Set.fold fold comp None with MultipleFound -> None in
  Pretype_errors.unsatisfiable_constraints env evd ev comp

(** Deprecated *)

let solve_one_instance = CRef.ref (fun env evm t -> assert false)

let resolve_one_typeclass ?unique:_ env evm t =
  let open CRef in
  !solve_one_instance env evm t

let set_solve_one_instance f = CRef.(solve_one_instance := f)
