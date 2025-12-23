(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* File created by Vincent Siles, Oct 2007, extended into a generic
   support for generation of inductive schemes by Hugo Herbelin, Nov 2009 *)

(* This file provides support for registering inductive scheme builders,
   declaring schemes and generating schemes on demand *)

open Names
open Nameops
open Declarations
open Constr
open Util

(**********************************************************************)
(* Registering schemes in the environment *)

type handle = Evd.side_effects

let push_handle eff =
  let open Proofview.Notations in
  Proofview.tclEVARMAP >>= fun sigma ->
  let sigma = Evd.emit_side_effects eff sigma in
  Proofview.Unsafe.tclEVARS sigma

(* Scheme builders. [bool] = is_dep. [None] = silent failure. *)
type mutual_scheme_object_function =
  Environ.env -> handle -> inductive list -> bool -> constr array Evd.in_ustate option
type individual_scheme_object_function =
  Environ.env -> handle -> inductive -> bool -> constr Evd.in_ustate option

module Key = DeclareScheme.Key

(* scheme_name * sort * is_mutual *)
type 'a scheme_kind = Key.t

let pr_scheme_kind (kind : Key.t) =
  let (str_list, opt_str,b) = kind in
  let pr_list = Pp.prlist Pp.str str_list in
  let pr_option = match opt_str with
    | Some s -> Pp.str (" (" ^ (UnivGen.QualityOrSet.family_to_str s) ^ ")")
    | None -> Pp.str " (None)"
  in
  Pp.(pr_list ++ pr_option)

(**********************************************************************)
(* The table of scheme building functions *)

type individual
type mutual

(* Dependency of a scheme on another scheme: (inductive, kind, internal) *)
type scheme_dependency =
  | SchemeMutualDep of Names.MutInd.t * mutual scheme_kind * bool
  | SchemeIndividualDep of inductive * individual scheme_kind * bool

type scheme_object_function =
  | MutualSchemeFunction of mutual_scheme_object_function * (Environ.env -> Names.MutInd.t -> bool -> scheme_dependency list) option
  | IndividualSchemeFunction of individual_scheme_object_function * (Environ.env -> inductive -> bool -> scheme_dependency list) option

let scheme_object_table =
  (Hashtbl.create 17 :
     (Key.t, (one_inductive_body option -> string) * scheme_object_function)
  Hashtbl.t)

let key_str key =
  let (str_list, opt_str,b) = key in
  let str_list = String.concat " " str_list in
  let str_option = match opt_str with
    | Some s -> " (" ^ (UnivGen.QualityOrSet.family_to_str s) ^ ")"
    | None -> " (None)"
  in
  str_list ^ str_option

let declare_scheme_object key suff f =
  let () =
    if not (Id.is_valid ("ind_" ^ suff None)) then
      CErrors.user_err Pp.(str ("Illegal induction scheme suffix: " ^ suff None))
  in
  if Hashtbl.mem scheme_object_table key then
    CErrors.user_err
      Pp.(str "Scheme object " ++ str (key_str key) ++ str " already declared.")
  else begin
    Hashtbl.add scheme_object_table key (suff,f);
    key
  end

let declare_mutual_scheme_object key suff ?deps f =
  let (strl,sortf) = key in
  let key = (strl,sortf,true) in
  declare_scheme_object key suff (MutualSchemeFunction (f, deps))

let declare_individual_scheme_object key suff ?deps f =
  let (strl,sortf) = key in
  let key = (strl,sortf,false) in
  declare_scheme_object key suff (IndividualSchemeFunction (f, deps))

let is_declared_scheme_object key = Hashtbl.mem scheme_object_table key

let get_suff sch_type sch_sort =
  try
    fst (
      match sch_sort with
      | Some st -> Hashtbl.find scheme_object_table (sch_type,sch_sort,true)
      | None -> Hashtbl.find scheme_object_table (sch_type,Some UnivGen.QualityOrSet.qtype,true)
      )
  with Not_found ->
    fst (match sch_sort with
      | Some st -> Hashtbl.find scheme_object_table (sch_type,sch_sort,false)
      | None -> Hashtbl.find scheme_object_table (sch_type,Some UnivGen.QualityOrSet.qtype,false)
       )

(**********************************************************************)
(* Defining/retrieving schemes *)

let is_visible_name id =
  try ignore (Nametab.locate (Libnames.qualid_of_ident id)); true
  with Not_found ->
    (* FIXME: due to private constant declaration being imperative, we have to
       also check in the global env *)
    Global.exists_objlabel id

let compute_name internal id avoid =
  if internal then
    let visible id = is_visible_name id || Id.Set.mem id avoid in
    Namegen.next_ident_away_from (add_prefix "internal_" id) visible
  else id

let declare_definition_scheme = ref (fun ~univs ~role ~name ~effs c ->
    CErrors.anomaly (Pp.str "scheme declaration not registered"))

let register_definition_scheme = ref (fun ~internal ~name ~const ~univs ?loc () ->
  CErrors.anomaly (Pp.str "scheme registering not registered"))

let lookup_scheme kind ind =
  try Some (DeclareScheme.lookup_scheme kind ind) with Not_found -> None

type schemes = {
  sch_eff : Evd.side_effects;
  sch_reg : (Id.t * Constant.t * Loc.t option * UState.named_universes_entry) list;
}

let empty_schemes eff = {
  sch_eff = eff;
  sch_reg = [];
}

let redeclare_schemes { sch_eff = eff } =
  let fold c role accu = match role with
  | Evd.Schema (ind, kind) ->
    try
      let _ = DeclareScheme.lookup_scheme kind ind in
      accu
    with Not_found ->
      let old = try Key.Map.find kind accu with Not_found -> [] in
      Key.Map.add kind ((ind, GlobRef.ConstRef c) :: old) accu
  in
  let schemes = Cmap_env.fold fold (Evd.seff_roles eff) Key.Map.empty in
  let iter kind defs = List.iter (DeclareScheme.declare_scheme SuperGlobal kind) defs in
  Key.Map.iter iter schemes

let local_lookup_scheme eff kind ind = match lookup_scheme kind ind with
| Some _ as ans -> ans
| None ->
  let exception Found of Constant.t in
  let iter c role = match role with
    | Evd.Schema (i, k) ->
      if Key.equal k kind && Ind.UserOrd.equal i ind then raise (Found c)
  in
  (* Inefficient O(n), but the number of locally declared schemes is small and
     this is very rarely called *)
  try let _ = Cmap_env.iter iter (Evd.seff_roles eff) in None with Found c -> Some (GlobRef.ConstRef c)

let local_check_scheme kind ind { sch_eff = eff } =
  Option.has_some (local_lookup_scheme eff kind ind)

let define ?loc internal role id c poly uctx sch =
  let avoid = Safe_typing.constants_of_private (Evd.seff_private sch.sch_eff) in
  let avoid = Id.Set.of_list @@ List.map (fun cst -> Constant.label cst) avoid in
  let id = compute_name internal id avoid in
  let uctx = UState.collapse_above_prop_sort_variables ~to_prop:true uctx in
  let uctx = UState.normalize_variables uctx in
  let uctx = UState.minimize uctx in
  let c = UState.nf_universes uctx c in
  let uctx = UState.restrict uctx (Vars.universes_of_constr c) in
  let univs = UState.univ_entry ~poly uctx in
  let effs = sch.sch_eff in
  let cst, effs = !declare_definition_scheme ~univs ~role ~name:id ~effs c in
  let reg = (id, cst, loc, univs) :: sch.sch_reg in
  cst, { sch_eff = effs; sch_reg = reg }

module Locmap : sig

    type t

    val default : Loc.t option -> t
    val make : ?default:Loc.t -> MutInd.t -> Loc.t option list -> t
    val lookup : locmap:t -> Names.inductive -> Loc.t option

end = struct

    type t = {
      default : Loc.t option;
      mind : MutInd.t option;
      ind_to_loc : Loc.t Int.Map.t;
    }

    let lookup ~locmap:{ ind_to_loc; default; mind } (m, i) =
      let () = match mind with
      | None -> ()
      | Some mind -> assert (MutInd.UserOrd.equal mind m)
      in
      Int.Map.find_opt i ind_to_loc |> fun loc ->
      Option.append loc default

    let default default = { default; ind_to_loc = Int.Map.empty; mind = None }

    let make ?default mind locs =
      let default, ind_to_loc =
        CList.fold_left_i (fun i (default,m) loc ->
          let m = match loc with
            | None -> m
            | Some loc -> Int.Map.add i loc m
          in
          let default = if Option.has_some default then default else loc in
          default, m)
          0 (default, Int.Map.empty) locs in
      { default; ind_to_loc; mind = Some mind }

  end

let get_env sch =
  Safe_typing.env_of_safe_env (Evd.get_senv_side_effects sch.sch_eff)

let globally_declare_schemes sch =
  Global.Internal.reset_safe_env (Evd.get_senv_side_effects sch.sch_eff)

(* Assumes that dependencies are already defined *)
let rec define_individual_scheme_base ?loc kind suff f ~internal idopt (mind,i as ind) eff =
  let env = get_env eff in
  match f env eff.sch_eff ind internal with
    | None -> None
    | Some (c, ctx) -> 
      let mib = Environ.lookup_mind mind env in
      let id = match idopt with
        | Some id -> id
        | None -> Id.of_string (suff (Some mib.mind_packets.(i))) in
      let role = Evd.Schema (ind, kind) in
      let poly, cumulative = Declareops.inductive_is_polymorphic mib, Declareops.inductive_is_cumulative mib in
      let poly = PolyFlags.make ~univ_poly:poly ~cumulative ~collapse_sort_variables:true in
      let const, eff = define ?loc internal role id c poly ctx eff in
      Some (const, eff)

and define_individual_scheme ?loc kind ~internal names (mind,i as ind) eff =
  match Hashtbl.find scheme_object_table kind with
  | _,MutualSchemeFunction _ -> assert false
  | s,IndividualSchemeFunction (f, deps) ->
    let env = get_env eff in
    let deps = match deps with None -> [] | Some deps -> deps env ind true in
    match Option.List.fold_left (fun eff dep -> declare_scheme_dependence eff dep) eff deps with
    | None -> CErrors.user_err Pp.(str "Problems were found during definition of scheme dependences.")
    | Some eff -> define_individual_scheme_base ?loc kind s f ~internal names ind eff

(* Assumes that dependencies are already defined *)
and define_mutual_scheme_base ?(locmap=Locmap.default None) kind suff f ~internal names inds eff =
  let env = get_env eff in
  let mind = (fst (List.hd inds)) in
  match f env eff.sch_eff inds internal with
    | None -> None
    | Some (cl, ctx) -> 
      let mib = Environ.lookup_mind mind env in
      let ids =
        if Array.length cl <> List.length names then
          Array.init (Array.length mib.mind_packets) (fun i ->
              try (i,Int.List.assoc i names)
              with Not_found -> (i,Id.of_string (suff (Some mib.mind_packets.(i)))))
        else
          Array.of_list names
      in
      let fold i effs id cl =
        let role = Evd.Schema ((mind, i), kind)in
        let loc = Locmap.lookup ~locmap (mind,i) in
        (* FIXME cumulativity not supported? *)
        let poly = PolyFlags.of_univ_poly (Declareops.inductive_is_polymorphic mib) in
        let cst, effs = define ?loc internal role id cl poly ctx effs in
        (effs, cst)
      in
      let (eff, consts) = Array.fold_left2_map_i fold eff ids cl in
      Some (consts, eff)
    
and define_mutual_scheme ?locmap kind ~internal names inds eff =
  let (strl,sortf,mutual) = kind in
  let kind = match sortf with Some k -> (strl,sortf,true) | None -> (strl,Some UnivGen.QualityOrSet.qtype,true) in 
  match Hashtbl.find scheme_object_table kind with
  | _,IndividualSchemeFunction _ -> assert false
  | s,MutualSchemeFunction (f, deps) ->
    let env = get_env eff in
    let mind = (fst (List.hd inds)) in
    let deps = match deps with None -> [] | Some deps -> deps env mind internal in
    match Option.List.fold_left (fun eff dep -> declare_scheme_dependence eff dep) eff deps with
    | None -> CErrors.user_err Pp.(str "Problems were found during definition of scheme dependences.")
    | Some eff -> define_mutual_scheme_base ?locmap kind s f ~internal names inds eff

and declare_scheme_dependence eff sd =
match sd with
| SchemeIndividualDep (ind, kind, intern) ->
  if local_check_scheme kind ind eff then Some eff
  else
    begin match define_individual_scheme kind ~internal:intern None ind eff with
      | None -> None
      | Some (_, eff') -> Some eff'
    end
| SchemeMutualDep (ind, kind, intern) ->
  if local_check_scheme kind (ind,0) eff then Some eff
  else
    begin match define_mutual_scheme kind ~internal:intern [] [(ind,0)] eff with
      | None -> None
      | Some (_, eff') -> Some eff'
    end

let find_scheme kind (mind,i as ind) =
  let open Proofview.Notations in
  Proofview.tclEVARMAP >>= fun sigma ->
  let s = local_lookup_scheme (Evd.eval_side_effects sigma) kind ind in
  Proofview.tclUNIT s

let force_find_scheme kind (mind,i as ind) =
  let open Proofview.Notations in
  Proofview.tclEVARMAP >>= fun sigma ->
  let eff = Evd.eval_side_effects sigma in
  match local_lookup_scheme eff kind ind with
  | Some s ->
    Proofview.tclUNIT s
  | None ->
    let senv = Evd.get_senv_side_effects eff in
    try
      let eff, ans = match Hashtbl.find scheme_object_table kind with
      | s,IndividualSchemeFunction (f, deps) ->
        let env = Safe_typing.env_of_safe_env senv in
        let deps = match deps with None -> [] | Some deps -> deps env ind true in
        let sch = empty_schemes eff in
        begin match Option.List.fold_left (fun eff dep -> declare_scheme_dependence eff dep) sch deps with
          | None -> assert false
          | Some eff -> 
            begin match define_individual_scheme_base kind s f ~internal:true None ind eff with
              | None -> assert false
              | Some (c, eff) -> 
                eff, c
            end
        end
      | s,MutualSchemeFunction (f, deps) ->
        let env = Safe_typing.env_of_safe_env senv in
        let deps = match deps with None -> [] | Some deps -> deps env mind true in
        let sch = empty_schemes eff in
        begin match Option.List.fold_left (fun eff dep -> declare_scheme_dependence eff dep) sch deps with
          | None -> assert false
          | Some eff -> 
            begin match define_mutual_scheme_base kind s f ~internal:true [] [mind,i] eff with
              | None -> assert false
              | Some (ca, eff) -> 
                eff, ca.(i)
            end
        end
      in
      let sigma = Evd.emit_side_effects eff.sch_eff sigma in
      Proofview.Unsafe.tclEVARS sigma <*> Proofview.tclUNIT (GlobRef.ConstRef ans)
    with Rocqlib.NotFoundRef _ as e ->
      let e, info = Exninfo.capture e in
      Proofview.tclZERO ~info e

let register_schemes sch =
  let iter (id, kn, loc, univs) =
    !register_definition_scheme ~internal:false ~name:id ~const:kn ~univs ?loc ()
  in
  List.iter iter (List.rev sch.sch_reg)

let define_individual_scheme ?loc ?(intern=false) kind names ind =
  let sch = empty_schemes Evd.empty_side_effects in
  match define_individual_scheme ?loc kind ~internal:intern names ind sch with
    | None -> ()
    | Some (_ , eff) ->
       let () = globally_declare_schemes eff in
       let () = register_schemes eff in
       redeclare_schemes eff

let define_mutual_scheme ?locmap ?(intern=false) kind names inds =
  let sch = empty_schemes Evd.empty_side_effects in
  match define_mutual_scheme ?locmap kind ~internal:intern names inds sch with
    | None -> ()
    | Some (_ , eff) ->
       let () = globally_declare_schemes eff in
       let () = register_schemes eff in
       redeclare_schemes eff
