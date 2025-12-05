(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Names
open Univ
open Sorts
open UVars

let template_default_univs = Summary.ref ~name:"template default univs" Univ.Level.Set.empty

let cache_template_default_univs us =
  template_default_univs := Univ.Level.Set.union !template_default_univs us

let template_default_univs_obj =
  Libobject.declare_object {
    (Libobject.default_object "template default univs") with
    cache_function = cache_template_default_univs;
    load_function = (fun _ us -> cache_template_default_univs us);
    discharge_function = (fun x -> Some x);
    classify_function = (fun _ -> Escape);
  }

let add_template_default_univs env kn =
  match (Environ.lookup_mind kn env).mind_template with
  | None -> ()
  | Some template ->
    let _, us = UVars.Instance.levels template.template_defaults in
    Lib.add_leaf (template_default_univs_obj us)

let template_default_univs () = !template_default_univs

module UnivFlex = UnivFlex

type universes_entry =
| Monomorphic_entry of Univ.ContextSet.t
| Polymorphic_entry of UVars.UContext.t

module UNameMap = Id.Map

type uinfo = {
  uname : Id.t option;
  uloc : Loc.t option;
}

open Quality

let sort_inconsistency ?explain cst l r =
  let explain = Option.map (fun p -> UGraph.Other p) explain in
  raise (UGraph.UniverseInconsistency (None, (cst, l, r, explain)))

module QSet = QVar.Set
module QMap = QVar.Map

module QState : sig
  type t
  type elt = QVar.t
  val empty : t
  val union : fail:(t -> Quality.t -> Quality.t -> t) -> t -> t -> t
  val add : check_fresh:bool -> rigid:bool -> elt -> t -> t
  val repr : elt -> t -> Quality.t
  val is_rigid : t -> QVar.t -> bool
  val is_above_prop : t -> QVar.t -> bool
  val unify_quality : fail:(unit -> t) -> Conversion.conv_pb -> Quality.t -> Quality.t -> t -> t
  val undefined : t -> QVar.Set.t
  val collapse_above_prop : to_prop:bool -> t -> t
  val collapse : ?except:QVar.Set.t -> t -> t
  val pr : (QVar.t -> Libnames.qualid option) -> t -> Pp.t
  val of_elims : QGraph.t -> t
  val elims : t -> QGraph.t
  val set_elims : QGraph.t -> t -> t
  val initial_elims : t -> QGraph.t
  val merge_constraints : (QGraph.t -> QGraph.t) -> t -> t
  val normalize_elim_constraints : t -> ElimConstraints.t -> ElimConstraints.t
end =
struct

type t = {
  rigid : QSet.t;
  (** Rigid variables, may not be set to another *)
  qmap : Quality.t option QMap.t;
  (* TODO: use a persistent union-find structure *)
  above_prop : QSet.t;
  (** Set for quality variables known to be either in Prop or Type.
      If q ∈ above_prop then it must map to None in qmap. *)
  elims : QGraph.t;
  (** Elimination graph for quality variables. *)
  initial_elims : QGraph.t;
  (** Keep the qvar domain without any constraints to optimize computation. *)
}

type elt = QVar.t

let empty = { rigid = QSet.empty; qmap = QMap.empty; above_prop = QSet.empty;
              elims = QGraph.initial_graph; initial_elims = QGraph.initial_graph }

let rec repr q m = match QMap.find q m.qmap with
| None -> QVar q
| Some (QVar q) -> repr q m
| Some (QConstant _ as q) -> q
| exception Not_found -> QVar q

let is_above_prop m q = QSet.mem q m.above_prop

let eliminates_to_prop m q =
  QGraph.eliminates_to_prop m.elims (QVar q)

let is_rigid m q = QSet.mem q m.rigid || not (QMap.mem q m.qmap)

let set q qv m =
  let q = repr q m in
  let q = match q with QVar q -> q | QConstant _ -> assert false in
  let qv = match qv with QVar qv -> repr qv m | (QConstant _ as qv) -> qv in
  match q, qv with
  | q, QVar qv ->
    if QVar.equal q qv then Some m
    else
    if QSet.mem q m.rigid then None
    else
      let above_prop =
        if is_above_prop m q
        then QSet.add qv (QSet.remove q m.above_prop)
        else m.above_prop in
      Some { rigid = m.rigid; qmap = QMap.add q (Some (QVar qv)) m.qmap; above_prop;
             elims = QGraph.enforce_eq (QVar qv) (QVar q) m.elims; initial_elims = m.initial_elims }
  | q, (QConstant qc as qv) ->
    if qc == QSProp && (is_above_prop m q || eliminates_to_prop m q) then None
    else if QSet.mem q m.rigid then None
    else
      Some { m with rigid = m.rigid; qmap = QMap.add q (Some qv) m.qmap;
                    above_prop = QSet.remove q m.above_prop;
                    elims = QGraph.enforce_eq qv (QVar q) m.elims }

let set_above_prop q m =
  let q = repr q m in
  let q = match q with QVar q -> q | QConstant _ -> assert false in
  if QSet.mem q m.rigid then None
  else Some { m with above_prop = QSet.add q m.above_prop }

let unify_quality ~fail c q1 q2 local = match q1, q2 with
| QConstant QType, QConstant QType
| QConstant QProp, QConstant QProp
| QConstant QSProp, QConstant QSProp -> local
| QConstant QProp, QVar q when c == Conversion.CUMUL ->
  begin match set_above_prop q local with
  | Some local -> local
  | None -> fail ()
  end
| QVar qv1, QVar qv2 -> begin match set qv1 q2 local with
    | Some local -> local
    | None -> match set qv2 q1 local with
      | Some local -> local
      | None -> fail ()
  end
| QVar q, (QConstant (QType | QProp | QSProp) as qv)
| (QConstant (QType | QProp | QSProp) as qv), QVar q ->
  begin match set q qv local with
  | Some local -> local
  | None -> fail ()
  end
| (QConstant QType, QConstant (QProp | QSProp)) -> fail ()
| (QConstant QProp, QConstant QType) ->
  begin match c with
  | CONV -> fail ()
  | CUMUL -> local
  end
| (QConstant QSProp, QConstant (QType | QProp)) -> fail ()
| (QConstant QProp, QConstant QSProp) -> fail ()

let nf_quality m = function
  | QConstant _ as q -> q
  | QVar q -> repr q m

let add_qvars m qmap qs =
  let g = m.initial_elims in
  let filter v = match QMap.find v qmap with
    | None | exception Not_found -> true
    | _ -> false in
  (* Here, we filter instead of enforcing equality due to the collapse:
     simply enforcing equality may lead to inconsistencies after it *)
  let qs = QVar.Set.filter filter qs in
  let fold v g = try QGraph.add_quality (QVar v) g with QGraph.AlreadyDeclared -> g in
  QVar.Set.fold fold qs g

let union ~fail s1 s2 =
  let extra = ref [] in
  let qmap = QMap.union (fun qk q1 q2 ->
      match q1, q2 with
      | Some q, None | None, Some q -> Some (Some q)
      | None, None -> Some None
      | Some q1, Some q2 ->
        let () = if not (Quality.equal q1 q2) then extra := (q1,q2) :: !extra in
        Some (Some q1))
      s1.qmap s2.qmap
  in
  let extra = !extra in
  let qs = QVar.Set.union (QGraph.qvar_domain s1.elims) (QGraph.qvar_domain s2.elims) in
  let filter v = match QMap.find v qmap with
    | None | exception Not_found -> true
    | _ -> false in
  let above_prop = QSet.filter filter @@ QSet.union s1.above_prop s2.above_prop in
  let elims = add_qvars s2 qmap qs in
  let s = { rigid = QSet.union s1.rigid s2.rigid; qmap; above_prop;
            elims; initial_elims = elims } in
  List.fold_left (fun s (q1,q2) ->
      let q1 = nf_quality s q1 and q2 = nf_quality s q2 in
      unify_quality ~fail:(fun () -> fail s q1 q2) CONV q1 q2 s)
    s
    extra

let add ~check_fresh ~rigid q m =
  if check_fresh then assert (not (QMap.mem q m.qmap));
  let add_quality g =
    try QGraph.add_quality (QVar q) g
    with QGraph.AlreadyDeclared as e -> if check_fresh then raise e else g
  in
  { rigid = if rigid then QSet.add q m.rigid else m.rigid;
    qmap = QMap.add q None m.qmap;
    above_prop = m.above_prop;
    elims = add_quality m.elims;
    initial_elims = add_quality m.initial_elims }

let of_elims elims =
  let qs = QGraph.qvar_domain elims in
  let initial_elims =
    QSet.fold (fun v -> QGraph.add_quality (QVar v)) qs (QGraph.initial_graph) in
  let initial_elims = QGraph.update_rigids elims initial_elims in
  { empty with rigid = qs; elims; initial_elims }

(* XXX what about qvars in the elimination graph? *)
let undefined m =
  let mq = QMap.filter (fun _ v -> Option.is_empty v) m.qmap in
  QMap.domain mq

let collapse_above_prop ~to_prop m =
  QMap.fold (fun q v m ->
           match v with
           | Some _ -> m
           | None ->
              if not @@ is_above_prop m q then m else
                if to_prop then Option.get (set q qprop m)
                else Option.get (set q qtype m)
         )
         m.qmap m

let collapse ?(except=QSet.empty) m =
  QMap.fold (fun q v m ->
           match v with
           | Some _ -> m
           | None -> if QSet.mem q m.rigid || QSet.mem q except then m
                    else Option.get (set q qtype m))
         m.qmap m

let pr prqvar_opt ({ qmap; elims; rigid } as m) =
  let open Pp in
  let prqvar q = match prqvar_opt q with
    | None -> QVar.raw_pr q
    | Some qid -> Libnames.pr_qualid qid
  in
  let prbody u = function
  | None ->
    if is_above_prop m u then str " >= Prop"
    else if QSet.mem u rigid then
      str " (rigid)"
    else mt ()
  | Some q ->
    let q = Quality.pr prqvar q in
    str " := " ++ q
  in
  let prqvar_name q =
    match prqvar_opt q with
    | None -> mt()
    | Some qid -> str " (named " ++ Libnames.pr_qualid qid ++ str ")"
  in
  h (prlist_with_sep fnl (fun (u, v) -> QVar.raw_pr u ++ prbody u v ++ prqvar_name u) (QMap.bindings qmap))

let elims m = m.elims

let set_elims elims m = { m with elims }

let initial_elims m = m.initial_elims

let merge_constraints f m =
  { m with elims = f m.elims }

let normalize_elim_constraints m cstrs =
  let subst q = match q with
    | QConstant _ -> q
    | QVar qv -> repr qv m
  in
  let is_instantiated q = is_qconst q || is_qglobal q in
  let can_drop (q1,_,q2) = not (is_instantiated q1 && is_instantiated q2) in
  let subst_cst (q1,c,q2) = (subst q1,c,subst q2) in
  let cstrs = ElimConstraints.map subst_cst cstrs in
  ElimConstraints.filter can_drop cstrs
end

module UPairSet = UnivMinim.UPairSet

type univ_names = UnivNames.universe_binders * (uinfo QVar.Map.t * uinfo Level.Map.t)

(* 2nd part used to check consistency on the fly. *)
type t =
 { names : univ_names; (** Printing/location information *)
   local : PConstraints.ContextSet.t; (** The local graph of universes (variables and constraints) *)
   univ_variables : UnivFlex.t;
   (** The local universes that are unification variables *)
   sort_variables : QState.t;
   (** Local quality variables. *)
   universes : UGraph.t; (** The current graph extended with the local constraints *)
   initial_universes : UGraph.t; (** The graph at the creation of the evar_map + local universes
                                     (but not local constraints) *)
   minim_extra : UnivMinim.extra;
 }

let empty =
  { names = UnivNames.empty_binders, (QMap.empty, Level.Map.empty);
    local = PConstraints.ContextSet.empty;
    univ_variables = UnivFlex.empty;
    sort_variables = QState.empty;
    universes = UGraph.initial_universes;
    initial_universes = UGraph.initial_universes;
    minim_extra = UnivMinim.empty_extra; }

let make ~qualities univs =
  { empty with
    universes = univs;
    initial_universes = univs ;
    sort_variables = QState.of_elims qualities
  }

let is_empty uctx =
  PConstraints.ContextSet.is_empty uctx.local &&
  UnivFlex.is_empty uctx.univ_variables

let id_of_level uctx l =
  try (Level.Map.find l (snd (snd uctx.names))).uname
  with Not_found -> None

let id_of_qvar uctx l =
  try (QVar.Map.find l (fst (snd uctx.names))).uname
  with Not_found -> None

let is_rigid_qvar uctx q = QState.is_rigid uctx.sort_variables q

let get_uname info = match info.uname with
| None -> raise Not_found
| Some id -> id

let qualid_of_qvar_names (bind, (qrev,_)) l =
  try Some (Libnames.qualid_of_ident (get_uname (QVar.Map.find l qrev)))
  with Not_found ->
    UnivNames.qualid_of_quality bind l

let qualid_of_level_names (bind, (_,urev)) l =
  try Some (Libnames.qualid_of_ident (get_uname (Level.Map.find l urev)))
  with Not_found ->
    UnivNames.qualid_of_level bind l

let qualid_of_level uctx l = qualid_of_level_names uctx.names l

let pr_uctx_qvar_names names l =
  match qualid_of_qvar_names names l with
  | Some qid -> Libnames.pr_qualid qid
  | None -> QVar.raw_pr l

let pr_uctx_level_names names l =
  match qualid_of_level_names names l with
  | Some qid -> Libnames.pr_qualid qid
  | None -> Level.raw_pr l

let pr_uctx_level uctx l = pr_uctx_level_names uctx.names l

let pr_uctx_qvar uctx l = pr_uctx_qvar_names uctx.names l

let merge_univ_constraints uctx cstrs g =
  try UGraph.merge_constraints cstrs g
  with UGraph.UniverseInconsistency (_, i) ->
    let printers = (pr_uctx_qvar uctx, pr_uctx_level uctx) in
    raise (UGraph.UniverseInconsistency (Some printers, i))

let merge_elim_constraints src uctx cstrs g =
  try QGraph.merge_constraints src cstrs g
  with QGraph.(EliminationError (QualityInconsistency (_, i))) ->
    let printer = pr_uctx_qvar uctx in
    raise (QGraph.(EliminationError (QualityInconsistency (Some printer, i))))

let uname_union s t =
  if s == t then s
  else
    UNameMap.merge (fun k l r ->
        match l, r with
        | Some _, _ -> l
        | _, _ -> r) s t

let names_union ((qbind,ubind),(qrev,urev)) ((qbind',ubind'),(qrev',urev')) =
  let qbind = uname_union qbind qbind'
  and ubind = uname_union ubind ubind'
  and qrev = QVar.Map.union (fun _ l _ -> Some l) qrev qrev'
  and urev = Level.Map.lunion urev urev' in
  ((qbind,ubind),(qrev,urev))

let union uctx uctx' =
  if uctx == uctx' then uctx
  else if is_empty uctx' then uctx
  else
    let local = PConstraints.ContextSet.union uctx.local uctx'.local in
    let names = names_union uctx.names uctx'.names in
    let newus = Level.Set.diff (PConstraints.ContextSet.levels uctx'.local)
                               (PConstraints.ContextSet.levels uctx.local) in
    let newus = Level.Set.diff newus (UnivFlex.domain uctx.univ_variables) in
    let extra = UnivMinim.extra_union uctx.minim_extra uctx'.minim_extra in
    let declarenew g =
      Level.Set.fold (fun u g -> UGraph.add_universe u ~strict:false g) newus g
    in
    let fail_union s q1 q2 =
      if UGraph.type_in_type uctx.universes then s
      else CErrors.user_err
          Pp.(str "Could not merge universe contexts: could not unify" ++ spc() ++
             Quality.raw_pr q1 ++ strbrk " and " ++ Quality.raw_pr q2 ++ str ".")
    in
      { names;
        local = local;
        univ_variables =
          UnivFlex.biased_union uctx.univ_variables uctx'.univ_variables;
        (* FIXME: merge constraints from contextset *)
        sort_variables = QState.union ~fail:fail_union uctx.sort_variables uctx'.sort_variables;
        initial_universes = declarenew uctx.initial_universes;
        universes =
          (if local == uctx.local then uctx.universes
           else
             let cstrsr = PConstraints.ContextSet.univ_constraints uctx'.local in
             merge_univ_constraints uctx cstrsr (declarenew uctx.universes));
        minim_extra = extra}

let context_set uctx = uctx.local

let sort_context_set uctx =
  let us, csts = uctx.local in
  (QState.undefined uctx.sort_variables, us), csts

let constraints uctx = snd uctx.local

let compute_instance_binders uctx inst =
  let (qrev, urev) = snd uctx.names in
  let qinst, uinst = Instance.to_array inst in
  let qmap = function
    | QVar q ->
      begin try Name (get_uname (QVar.Map.find q qrev))
      with Not_found -> Anonymous
      end
    | QConstant _ -> assert false
  in
  let umap lvl =
    try Name (get_uname (Level.Map.find lvl urev))
    with Not_found -> Anonymous
  in
  {quals = Array.map qmap qinst; univs =  Array.map umap uinst}

let context uctx =
  let qvars = QState.undefined uctx.sort_variables in
  let (uvars, (qcst, ucst)) = uctx.local in
  UContext.of_context_set (compute_instance_binders uctx) ((qvars, qcst), (uvars, ucst))

type named_universes_entry = universes_entry * UnivNames.universe_binders

let check_mono_sort_constraints uctx =
  let (uvar, (qcst, ucst)) = uctx in
  (* This looks very stringent but it passes nonetheless all the tests? *)
  let () = assert (Sorts.ElimConstraints.is_empty qcst) in
  (uvar, ucst)

let univ_entry ~poly uctx =
  let (binders, _) = uctx.names in
  let entry =
    if poly then Polymorphic_entry (context uctx)
    else
      let uctx = check_mono_sort_constraints (context_set uctx) in
      Monomorphic_entry uctx
  in
  entry, binders

type universe_opt_subst = UnivFlex.t

let subst uctx = uctx.univ_variables
let ugraph uctx = uctx.universes

let elim_graph uctx = QState.elims uctx.sort_variables
let initial_elim_graph uctx = QState.initial_elims uctx.sort_variables

let is_above_prop uctx qv = QState.is_above_prop uctx.sort_variables qv

let is_algebraic l uctx = UnivFlex.is_algebraic l uctx.univ_variables

let of_names (ubind,(revqbind,revubind)) =
  let revqbind = QVar.Map.map (fun id -> { uname = Some id; uloc = None }) revqbind in
  let revubind = Level.Map.map (fun id -> { uname = Some id; uloc = None }) revubind in
  let qgraph = QVar.Map.fold (fun v _ -> QGraph.add_quality (QVar v)) revqbind QGraph.initial_graph in
  { empty with names = (ubind,(revqbind,revubind));
               sort_variables = QState.of_elims qgraph; }

let universe_of_name uctx s =
  UNameMap.find s (snd (fst uctx.names))

let quality_of_name uctx s =
  Id.Map.find s (fst (fst uctx.names))

let name_level level id uctx =
  let ((qbind,ubind),(qrev,urev)) = uctx.names in
  assert(not(Id.Map.mem id ubind));
  let ubind = Id.Map.add id level ubind in
  let urev = Level.Map.add level { uname = Some id; uloc = None } urev in
  { uctx with names = ((qbind,ubind),(qrev,urev)) }

let universe_binders uctx =
  let named, _ = uctx.names in
  named

let nf_qvar uctx q = QState.repr q uctx.sort_variables

let instantiate_variable l (b : Universe.t) v =
  v := UnivFlex.define l b !v

exception UniversesDiffer

let { Goptions.get = weak_constraints } =
  Goptions.declare_bool_option_and_ref
    ~key:["Cumulativity";"Weak";"Constraints"]
    ~value:true
    ()

let level_inconsistency cst l r =
  let mk u = Sorts.sort_of_univ @@ Universe.make u in
  raise (UGraph.UniverseInconsistency (None, (cst, mk l, mk r, None)))

let nf_universe uctx u =
  UnivSubst.(subst_univs_universe (UnivFlex.normalize_univ_variable uctx.univ_variables)) u

let nf_level uctx u =
  UnivSubst.(level_subst_of (UnivFlex.normalize_univ_variable uctx.univ_variables)) u

let nf_instance uctx u = Instance.subst_fn (nf_qvar uctx, nf_level uctx) u

let nf_quality uctx q = Quality.subst (nf_qvar uctx) q

let nf_sort uctx s =
  let normalize u = nf_universe uctx u in
  let qnormalize q = QState.repr q uctx.sort_variables in
  Sorts.subst_fn (qnormalize, normalize) s

let nf_relevance uctx r = match r with
| Relevant | Irrelevant -> r
| RelevanceVar q ->
  match nf_qvar uctx q with
  | QConstant QSProp -> Sorts.Irrelevant
  | QConstant QProp | QConstant QType -> Sorts.Relevant
  | QVar q' ->
    (* XXX currently not used in nf_evars_and_universes_opt_subst
       does it matter? *)
    if QState.is_above_prop uctx.sort_variables q' then Relevant
    else if QVar.equal q q' then r
    else Sorts.RelevanceVar q'

let nf_universes uctx c =
  let lsubst = uctx.univ_variables in
  let nf_univ u = UnivFlex.normalize_univ_variable lsubst u in
  let rec self () c = match Constr.kind c with
  | Evar (evk, args) ->
    let args' = SList.Smart.map (self ()) args in
    if args == args' then c else Constr.mkEvar (evk, args')
  | _ -> UnivSubst.map_universes_opt_subst_with_binders ignore self (nf_relevance uctx) (nf_qvar uctx) nf_univ () c
  in
  self ()  c

type small_universe = USet | UProp | USProp

let is_uset = function USet -> true | UProp | USProp -> false

type sort_classification =
| USmall of small_universe (* Set, Prop or SProp *)
| ULevel of Level.t (* Var or Global *)
| UMax of Universe.t * Level.Set.t (* Max of Set, Var, Global without increments *)
| UAlgebraic of Universe.t (* Arbitrary algebraic expression *)

let classify s = match s with
| Prop -> USmall UProp
| SProp -> USmall USProp
| Set -> USmall USet
| Type u | QSort (_, u) ->
  if Universe.is_levels u then match Universe.level u with
  | None -> UMax (u, Universe.levels u)
  | Some u -> ULevel u
  else UAlgebraic u

type local = {
  local_cst : PConstraints.t;
  local_above_prop : Level.Set.t;
  local_weak : UPairSet.t;
  local_sorts : QState.t;
}

let add_univ_local cst local =
  { local with local_cst = PConstraints.add_univ cst local.local_cst }

(* Constraint with algebraic on the left and a single level on the right *)
let enforce_leq_up u v local =
  let elim_csts = PConstraints.qualities local.local_cst in
  let univ_csts = UnivSubst.enforce_leq u (Universe.make v) @@
                    PConstraints.univs local.local_cst in
  { local with local_cst = PConstraints.make elim_csts univ_csts }

let get_constraint = function
| Conversion.CONV -> UnivConstraint.Eq
| Conversion.CUMUL -> UnivConstraint.Le

let warn_template =
  CWarnings.create_warning ~from:[CWarnings.CoreCategories.fragile] ~default:Disabled ~name:"bad-template-constraint" ()

let do_warn_template = CWarnings.create_in warn_template
    Pp.(fun (uctx,csts) ->
        str "Adding constraints involving global template univs:" ++ spc() ++
        UnivConstraints.pr (pr_uctx_level uctx) csts )

let warn_template uctx csts =
  match CWarnings.warning_status warn_template with
  | Disabled -> ()
  | Enabled | AsError ->
  let is_template u = Level.Set.mem u (template_default_univs()) in
  let csts = UnivConstraints.filter (fun (u,_,v as cst) ->
      not (Level.is_set u) && not (Level.is_set v) &&
      (is_template u || is_template v) &&
      not (UGraph.check_constraint uctx.universes cst)) csts in
  if not @@ UnivConstraints.is_empty csts then
    do_warn_template (uctx,csts)

let unify_quality univs c s1 s2 l =
  let fail () = if UGraph.type_in_type univs then l.local_sorts
    else sort_inconsistency (get_constraint c) s1 s2
  in
  { l with
    local_sorts = QState.unify_quality ~fail
        c (Sorts.quality s1) (Sorts.quality s2) l.local_sorts;
  }

let process_constraints uctx cstrs =
  let open UnivSubst in
  let open UnivProblem in
  let univs = uctx.universes in
  let quals = elim_graph uctx in
  let vars = ref uctx.univ_variables in
  let normalize u = UnivFlex.normalize_univ_variable !vars u in
  let qnormalize sorts q = QState.repr q sorts in
  let normalize_sort sorts s =
    Sorts.subst_fn ((qnormalize sorts), subst_univs_universe normalize) s
  in
  let nf_constraint sorts = function
    | QLeq (a, b) -> QLeq (Quality.subst (qnormalize sorts) a, Quality.subst (qnormalize sorts) b)
    | QEq (a, b) -> QEq (Quality.subst (qnormalize sorts) a, Quality.subst (qnormalize sorts) b)
    | ULub (u, v) -> ULub (level_subst_of normalize u, level_subst_of normalize v)
    | UWeak (u, v) -> UWeak (level_subst_of normalize u, level_subst_of normalize v)
    | UEq (u, v) -> UEq (normalize_sort sorts u, normalize_sort sorts v)
    | ULe (u, v) -> ULe (normalize_sort sorts u, normalize_sort sorts v)
  in
  let is_local l = UnivFlex.mem l !vars in
  let equalize_small l s local =
    let ls = match l with
    | USProp -> sprop
    | UProp -> prop
    | USet -> set
    in
    if UGraph.check_eq_sort quals univs ls s then local
    else if is_uset l then match classify s with
    | USmall _ -> sort_inconsistency Eq set s
    | ULevel r ->
      if is_local r then
        let () = instantiate_variable r Universe.type0 vars in
        add_univ_local (Level.set, Eq, r) local
      else
        sort_inconsistency Eq set s
    | UMax (u, _)| UAlgebraic u ->
      if univ_level_mem Level.set u then
        let inst = univ_level_rem Level.set u u in
        enforce_leq_up inst Level.set local
      else
        sort_inconsistency Eq ls s
    else sort_inconsistency Eq ls s
  in
  let equalize_variables fo l' r' local =
    if Level.equal l' r' then local
    else
      let () =
        if is_local l' then
          instantiate_variable l' (Universe.make r') vars
        else if is_local r' then
          instantiate_variable r' (Universe.make l') vars
        else if not (UnivProblem.check_eq_level univs l' r') then
          (* Two rigid/global levels, none of them being local,
              one of them being Prop/Set, disallow *)
          if Level.is_set l' || Level.is_set r' then
            level_inconsistency Eq l' r'
          else if fo then
            raise UniversesDiffer
      in
      add_univ_local (l', Eq, r') local
  in
  let equalize_algebraic l ru local =
    let alg = UnivFlex.is_algebraic l uctx.univ_variables in
    let inst = univ_level_rem l ru ru in
    if alg && not (Level.Set.mem l (Universe.levels inst)) then
      let () = instantiate_variable l inst vars in
      local
    else
      if univ_level_mem l ru then
        enforce_leq_up inst l local
      else sort_inconsistency Eq (sort_of_univ (Universe.make l)) (sort_of_univ ru)
  in
  let equalize_universes l r local = match classify l, classify r with
  | USmall l', (USmall _ | ULevel _ | UMax _ | UAlgebraic _) ->
    equalize_small l' r local
  | (ULevel _ | UMax _ | UAlgebraic _), USmall r' ->
    equalize_small r' l local
  | ULevel l', ULevel r' ->
    equalize_variables false l' r' local
  | ULevel l', (UAlgebraic r | UMax (r, _)) | (UAlgebraic r | UMax (r, _)), ULevel l' ->
    equalize_algebraic l' r local
  | (UAlgebraic _ | UMax _), (UAlgebraic _ | UMax _) ->
    (* both are algebraic *)
    if UGraph.check_eq_sort quals univs l r then local
    else sort_inconsistency Eq l r
  in
  let unify_universes cst local =
    let cst = nf_constraint local.local_sorts cst in
    if UnivProblem.is_trivial cst then local
    else
      (* TODO sort_inconsistency should be able to handle raw
         qualities instead of having to make a dummy sort *)
      let mk q = Sorts.make q Universe.type0 in
      match cst with
    | QEq (a, b) -> unify_quality univs CONV (mk a) (mk b) local
    | QLeq (a, b) -> unify_quality univs CUMUL (mk a) (mk b) local
    | ULe (l, r) ->
      let local = unify_quality univs CUMUL l r local in
      let l = normalize_sort local.local_sorts l in
      let r = normalize_sort local.local_sorts r in
      begin match classify r with
      | UAlgebraic _ | UMax _ ->
        if UGraph.check_leq_sort quals univs l r then local
        else
          sort_inconsistency Le l r
            ~explain:(Pp.str "(cannot handle algebraic on the right)")
      | USmall r' ->
        (* Invariant: there are no universes u <= Set in the graph. Except for
           template levels, Set <= u anyways. Otherwise, for template
           levels, any constraint u <= Set is turned into u := Set. *)
        if UGraph.type_in_type univs then local
        else begin match classify l with
        | UAlgebraic _ ->
          (* l contains a +1 and r=r' small so l <= r impossible *)
          sort_inconsistency Le l r
        | USmall l' ->
          if UGraph.check_leq_sort quals univs l r then local
          else sort_inconsistency Le l r
        | ULevel l' ->
          if is_uset r' && is_local l' then
            (* Unbounded universe constrained from above, we equalize it *)
            let () = instantiate_variable l' Universe.type0 vars in
            add_univ_local (l', Eq, Level.set) local
          else
            sort_inconsistency Le l r
        | UMax (_, levels) ->
          if is_uset r' then
            let fold l' local =
              let l = sort_of_univ @@ Universe.make l' in
              if Level.is_set l' || is_local l' then
                equalize_variables false l' Level.set local
              else sort_inconsistency Le l r
            in
            Level.Set.fold fold levels local
          else
            sort_inconsistency Le l r
        end
      | ULevel r' ->
        (* We insert the constraint in the graph even if the graph
            already contains it.  Indeed, checking the existence of the
            constraint is costly when the constraint does not already
            exist directly as a single edge in the graph, but adding an
            edge in the graph which is implied by others is cheap.
            Hence, by doing this, we avoid a costly check here, and
            make further checks of this constraint easier since it will
            exist directly in the graph. *)
        match classify l with
        | USmall UProp ->
          { local with local_above_prop = Level.Set.add r' local.local_above_prop }
        | USmall USProp ->
          if UGraph.type_in_type univs then local
          else sort_inconsistency Le l r
        | USmall USet ->
          add_univ_local (Level.set, Le, r') local
        | ULevel l' ->
          add_univ_local (l', Le, r') local
        | UAlgebraic l ->
          enforce_leq_up l r' local
        | UMax (_, l) ->
          Univ.Level.Set.fold (fun l' accu -> add_univ_local (l', Le, r') accu) l local
      end
    | ULub (l, r) ->
      equalize_variables true l r local
    | UWeak (l, r) ->
      if weak_constraints ()
      then { local with local_weak = UPairSet.add (l, r) local.local_weak }
      else local
    | UEq (l, r) ->
      let local = unify_quality univs CONV l r local in
      let l = normalize_sort local.local_sorts l in
      let r = normalize_sort local.local_sorts r in
      equalize_universes l r local
  in
  let unify_universes cst local =
    if not (UGraph.type_in_type univs) then unify_universes cst local
    else try unify_universes cst local with UGraph.UniverseInconsistency _ -> local
  in
  let local = {
    local_cst = PConstraints.empty;
    local_weak = uctx.minim_extra.UnivMinim.weak_constraints;
    local_above_prop = uctx.minim_extra.UnivMinim.above_prop;
    local_sorts = uctx.sort_variables;
  } in
  let local = UnivProblem.Set.fold unify_universes cstrs local in
  let extra = { UnivMinim.above_prop = local.local_above_prop; UnivMinim.weak_constraints = local.local_weak } in
  let () = warn_template uctx (PConstraints.univs local.local_cst) in
  !vars, extra, local.local_cst, local.local_sorts

let add_constraints src uctx cstrs elim_cstrs =
  let univs, local = uctx.local in
  let vars, extra, local', sorts = process_constraints uctx cstrs in
  let local' = PConstraints.union local' (PConstraints.of_qualities elim_cstrs) in
  { uctx with
    local = (univs, PConstraints.union local local');
    univ_variables = vars;
    universes = merge_univ_constraints uctx (PConstraints.univs local') uctx.universes;
    sort_variables =
          QState.merge_constraints (merge_elim_constraints src uctx (PConstraints.qualities local')) sorts ;
    minim_extra = extra; }

let problem_of_univ_constraints cstrs =
  UnivConstraints.fold (fun (l,d,r) acc ->
      let l = Universe.make l and r = sort_of_univ @@ Universe.make r in
      let cstr' = let open UnivProblem in
        match d with
        | Lt ->
          ULe (sort_of_univ @@ Universe.super l, r)
        | Le -> ULe (sort_of_univ l, r)
        | Eq -> UEq (sort_of_univ l, r)
      in UnivProblem.Set.add cstr' acc)
    cstrs UnivProblem.Set.empty

let problem_of_qcumul_constraints qcstrs =
  Sorts.QCumulConstraints.fold (fun (l,d,r) cstrs ->
      match d with
      | Eq -> UnivProblem.Set.add (QEq (l,r)) cstrs
      | Leq -> UnivProblem.Set.add (QLeq (l,r)) cstrs)
    qcstrs UnivProblem.Set.empty

let add_univ_constraints_gen src uctx cstrs elim_cstrs =
  let cstrs = problem_of_univ_constraints cstrs in
  add_constraints src uctx cstrs elim_cstrs

let add_univ_constraints uctx cstrs =
  add_univ_constraints_gen QGraph.Static uctx cstrs ElimConstraints.empty

let add_elim_constraints src uctx cstrs =
  add_constraints src uctx UnivProblem.Set.empty cstrs

let add_poly_constraints src uctx (qcstrs,ucstrs) =
  add_univ_constraints_gen src uctx ucstrs qcstrs

let add_quconstraints uctx (qcstrs,ucstrs) =
  let ucstrs = problem_of_univ_constraints ucstrs in
  let qcstrs = problem_of_qcumul_constraints qcstrs in
  (* Here the source shouldn't matter as there are no elim constraints *)
  add_constraints QGraph.Static uctx (UnivProblem.Set.union ucstrs qcstrs)
    ElimConstraints.empty

let check_qconstraints uctx csts =
  Sorts.QCumulConstraints.for_all (fun (l,k,r) ->
    let l = nf_quality uctx l in
    let r = nf_quality uctx r in
    match k with
    | Eq -> QGraph.check_eq (QState.elims uctx.sort_variables) l r
    | Leq ->
      match l, r with
      | QConstant QProp, QConstant QType -> true
      | _ -> QGraph.check_eq (QState.elims uctx.sort_variables) l r)
  csts

let check_elim_constraints uctx csts =
  Sorts.ElimConstraints.for_all (fun (l,k,r) ->
      let l = nf_quality uctx l in
      let r = nf_quality uctx r in
      match l,k,r with
        | _, Equal, _ -> Quality.equal l r
        | _, ElimTo, _ -> Inductive.eliminates_to (QState.elims uctx.sort_variables) l r)
    csts

let check_constraint uctx (c:UnivProblem.t) =
  match c with
  | QEq (a,b) ->
    let a = nf_quality uctx a in
    let b = nf_quality uctx b in
    Quality.equal a b
  | QLeq (a,b) ->
    let a = nf_quality uctx a in
    let b = nf_quality uctx b in
    Quality.equal a b ||
      begin
        match a, b with
        | QConstant QProp, QConstant QType -> true
        | QConstant QProp, QVar q -> QState.is_above_prop uctx.sort_variables q
        | (QConstant _ | QVar _), _ -> false
      end
  | ULe (u,v) -> UGraph.check_leq_sort (elim_graph uctx) uctx.universes u v
  | UEq (u,v) -> UGraph.check_eq_sort (elim_graph uctx) uctx.universes u v
  | ULub (u,v) -> UGraph.check_eq_level uctx.universes u v
  | UWeak _ -> true

let check_constraints uctx csts =
  UnivProblem.Set.for_all (check_constraint uctx) csts

let constrain_variables diff uctx =
  let local, vars = UnivFlex.constrain_variables diff uctx.univ_variables uctx.local in
  { uctx with local; univ_variables = vars }

type ('a, 'b, 'c, 'd) gen_universe_decl = {
  univdecl_qualities : 'a;
  univdecl_extensible_qualities : bool;
  univdecl_elim_constraints : 'b;
  univdecl_instance : 'c; (* Declared universes *)
  univdecl_extensible_instance : bool; (* Can new universes be added *)
  univdecl_univ_constraints : 'd; (* Declared univ constraints *)
  univdecl_extensible_constraints : bool; (* Can new constraints (elim or univ) be added *) }

type universe_decl =
  (QVar.t list, Sorts.ElimConstraints.t, Level.t list, Univ.UnivConstraints.t) gen_universe_decl

let default_univ_decl =
  { univdecl_qualities = [];
    (* in practice non named qualities will get collapsed for toplevel definitions,
       but side effects see named qualities from the surrounding definitions
       while using default_univ_decl *)
    univdecl_extensible_qualities = true;
    univdecl_elim_constraints = ElimConstraints.empty;
    univdecl_instance = [];
    univdecl_extensible_instance = true;
    univdecl_univ_constraints = UnivConstraints.empty;
    univdecl_extensible_constraints = true }

let univ_decl_csts decl =
  PConstraints.make decl.univdecl_elim_constraints decl.univdecl_univ_constraints

let pr_error_unbound_universes quals univs names =
  let open Pp in
  let nqs = QVar.Set.cardinal quals in
  let prqvar q =
    let info = QVar.Map.find_opt q (fst (snd names)) in
    h (pr_uctx_qvar_names names q ++ (match info with
        | None | Some {uloc=None} -> mt ()
        | Some {uloc=Some loc} -> spc() ++ str"(" ++ Loc.pr loc ++ str")"))
  in
  let nus = Level.Set.cardinal univs in
  let prlev u =
    let info = Level.Map.find_opt u (snd (snd names)) in
    h (pr_uctx_level_names names u ++ (match info with
        | None | Some {uloc=None} -> mt ()
        | Some {uloc=Some loc} -> spc() ++ str"(" ++ Loc.pr loc ++ str")"))
  in
  let ppqs = if nqs > 0 then
      str (if nqs = 1 then "Quality" else "Qualities") ++ spc () ++
      prlist_with_sep spc prqvar (QVar.Set.elements quals)
    else mt()
  in
  let ppus = if nus > 0 then
      let universe_s = CString.plural nus "universe" in
      let universe_s = if nqs = 0 then CString.capitalize_ascii universe_s else universe_s in
      str universe_s ++ spc () ++
      prlist_with_sep spc prlev (Level.Set.elements univs)
    else mt()
  in
  (hv 0
     (ppqs ++
      (if nqs > 0 && nus > 0 then strbrk " and " else mt()) ++
      ppus ++
      spc () ++ str (CString.conjugate_verb_to_be (nus + nqs)) ++ str" unbound."))

exception UnboundUnivs of QVar.Set.t * Level.Set.t * univ_names

(* XXX when we have multi location errors we won't have to pick an arbitrary error *)
let error_unbound_universes qs us uctx =
  let exception Found of Loc.t in
  let loc =
    try
      Level.Set.iter (fun u ->
          match Level.Map.find_opt u (snd (snd uctx)) with
          | None -> ()
          | Some info -> match info.uloc with
            | None -> ()
            | Some loc -> raise_notrace (Found loc))
        us;
      QVar.Set.iter (fun s ->
          match QVar.Map.find_opt s (fst (snd uctx)) with
          | None -> ()
          | Some info -> match info.uloc with
            | None -> ()
            | Some loc -> raise_notrace (Found loc))
        qs;
      None
    with Found loc -> Some loc
  in
  Loc.raise ?loc (UnboundUnivs (qs,us,uctx))

let () = CErrors.register_handler (function
    | UnboundUnivs (qs,us,uctx) -> Some (pr_error_unbound_universes qs us uctx)
    | _ -> None)

let universe_context_inst decl qvars levels names =
  let leftqs = List.fold_left (fun acc l -> QSet.remove l acc) qvars decl.univdecl_qualities in
  let leftus = List.fold_left (fun acc l -> Level.Set.remove l acc) levels decl.univdecl_instance in
  let () =
    let unboundqs = if decl.univdecl_extensible_qualities then QSet.empty else leftqs in
    let unboundus = if decl.univdecl_extensible_instance then Level.Set.empty else leftus in
    if not (QSet.is_empty unboundqs && Level.Set.is_empty unboundus)
    then error_unbound_universes unboundqs unboundus names
  in
  let leftqs = UContext.sort_qualities
      (Array.map_of_list (fun q -> Quality.QVar q) (QVar.Set.elements leftqs))
  in
  let leftus = UContext.sort_levels (Array.of_list (Level.Set.elements leftus)) in
  let instq = Array.append
      (Array.map_of_list (fun q -> QVar q) decl.univdecl_qualities)
      leftqs
  in
  let instu = Array.append (Array.of_list decl.univdecl_instance) leftus in
  let inst = Instance.of_array (instq,instu) in
  inst

let check_universe_context_set ~prefix levels names =
  let left =
    List.fold_left (fun left l -> Level.Set.remove l left)
      levels prefix
  in
  if not (Level.Set.is_empty left)
  then error_unbound_universes QVar.Set.empty left names

let check_univ_implication uctx cstrs cstrs' =
  let gr = uctx.initial_universes in
  let grext = merge_univ_constraints uctx cstrs gr in
  let cstrs' = UnivConstraints.filter (fun c -> not (UGraph.check_constraint grext c)) cstrs' in
  if UnivConstraints.is_empty cstrs' then ()
  else CErrors.user_err
      Pp.(str "Universe constraints are not implied by the ones declared: " ++
          UnivConstraints.pr (pr_uctx_level uctx) cstrs')

let check_elim_implication uctx cstrs cstrs' =
  let g = initial_elim_graph uctx in
  let grext = merge_elim_constraints QGraph.Rigid uctx cstrs g in
  let cstrs' = ElimConstraints.filter (fun c -> not (QGraph.check_constraint grext c)) cstrs' in
  if ElimConstraints.is_empty cstrs' then ()
  else CErrors.user_err
      Pp.(str "Elimination constraints are not implied by the ones declared: " ++
          ElimConstraints.pr (pr_uctx_qvar uctx) cstrs')

let check_implication uctx (elim_csts,univ_csts) (elim_csts',univ_csts') =
  check_univ_implication uctx univ_csts univ_csts';
  check_elim_implication uctx elim_csts elim_csts'

let check_template_univ_decl uctx ~template_qvars decl =
  let () =
    match List.filter (fun q -> not @@ QSet.mem q template_qvars) decl.univdecl_qualities with
    | (_ :: _) as qvars ->
      CErrors.user_err
        Pp.(str "Qualities " ++ prlist_with_sep spc (pr_uctx_qvar uctx) qvars ++
            str " cannot be template.")
    | [] ->
      if not (QVar.Set.equal template_qvars (QState.undefined uctx.sort_variables))
      then CErrors.anomaly Pp.(str "Bugged template univ declaration.")
  in
  let levels, csts = uctx.local in
  let () =
    let prefix = decl.univdecl_instance in
    if not decl.univdecl_extensible_instance
    then check_universe_context_set ~prefix levels uctx.names
  in
  if decl.univdecl_extensible_constraints then uctx.local
  else begin
    check_implication uctx
      (univ_decl_csts decl) csts;
    levels, (decl.univdecl_elim_constraints,decl.univdecl_univ_constraints)
  end

let check_mono_univ_decl uctx decl =
  (* Note: if [decl] is [default_univ_decl], behave like [uctx.local] *)
  let () =
    if not (List.is_empty decl.univdecl_qualities)
    || not (QSet.is_empty (QState.undefined uctx.sort_variables))
    then CErrors.user_err Pp.(str "Monomorphic declarations may not have sort variables.")
  in
  let levels, csts = uctx.local in
  let () =
    let prefix = decl.univdecl_instance in
    if not decl.univdecl_extensible_instance
    then check_universe_context_set ~prefix levels uctx.names
  in
  if decl.univdecl_extensible_constraints then check_mono_sort_constraints uctx.local
  else
    let () = assert (Sorts.ElimConstraints.is_empty (fst csts)) in
    let () = check_implication uctx (univ_decl_csts decl) csts in
    levels, decl.univdecl_univ_constraints

let check_poly_univ_decl uctx decl =
  (* Note: if [decl] is [default_univ_decl], behave like [context uctx] *)
  let levels, (elim_csts,univ_csts) = uctx.local in
  let qvars = QState.undefined uctx.sort_variables in
  let inst = universe_context_inst decl qvars levels uctx.names in
  let nas = compute_instance_binders uctx inst in
  let univ_csts = if decl.univdecl_extensible_constraints then univ_csts
    else begin
      check_univ_implication uctx
        decl.univdecl_univ_constraints
        univ_csts;
      decl.univdecl_univ_constraints
    end
  in
  let elim_csts = if decl.univdecl_extensible_constraints then elim_csts
    else begin
      check_elim_implication uctx
        decl.univdecl_elim_constraints
        elim_csts;
      decl.univdecl_elim_constraints
    end
  in
  let uctx = UContext.make nas (inst, (elim_csts,univ_csts)) in
  uctx

let check_univ_decl ~poly uctx decl =
  let (binders, _) = uctx.names in
  let entry =
    if poly then Polymorphic_entry (check_poly_univ_decl uctx decl)
    else Monomorphic_entry (check_mono_univ_decl uctx decl)
  in
  entry, binders

let restrict_universe_context (univs, csts) keep =
  let removed = Level.Set.diff univs keep in
  if Level.Set.is_empty removed then univs, csts
  else
  let elim_csts = PConstraints.qualities csts in
  let univ_csts = PConstraints.univs csts in
  let allunivs = UnivConstraints.fold (fun (u,_,v) all -> Level.Set.add u (Level.Set.add v all)) univ_csts univs in
  let g = UGraph.initial_universes in
  let g = Level.Set.fold (fun v g ->
      if Level.is_set v then g else
        UGraph.add_universe v ~strict:false g) allunivs g in
  let g = UGraph.merge_constraints univ_csts g in
  let allkept = Level.Set.union (UGraph.domain UGraph.initial_universes) (Level.Set.diff allunivs removed) in
  let univ_csts = UGraph.constraints_for ~kept:allkept g in
  let univ_csts = UnivConstraints.filter (fun (l,d,r) -> not (Level.is_set l && d == Le)) univ_csts in
  (Level.Set.inter univs keep, PConstraints.make elim_csts univ_csts)

let restrict uctx vars =
  let vars = Id.Map.fold (fun na l vars -> Level.Set.add l vars)
      (snd (fst uctx.names)) vars
  in
  let uctx' = restrict_universe_context uctx.local vars in
  { uctx with local = uctx' }

let restrict_even_binders uctx vars =
  let uctx' = restrict_universe_context uctx.local vars in
  { uctx with local = uctx' }

let restrict_univ_constraints uctx csts =
  let levels, (elim_csts,univ_csts) = uctx.local in
  let uctx' = { uctx with local = (levels,(elim_csts,UnivConstraints.empty)); universes = uctx.initial_universes } in
  add_univ_constraints uctx' csts

let restrict_elim_constraints src uctx csts =
  let levels, (elim_csts,univ_csts) = uctx.local in
  let g = initial_elim_graph uctx in
  let uctx' = { uctx with local = (levels,(ElimConstraints.empty,univ_csts));
                          sort_variables = QState.set_elims g uctx.sort_variables } in
  add_elim_constraints src uctx' csts


type rigid =
  | UnivRigid
  | UnivFlexible of bool (** Is substitution by an algebraic ok? *)

let univ_rigid = UnivRigid
let univ_flexible = UnivFlexible false
let univ_flexible_alg = UnivFlexible true

(** ~sideff indicates that it is ok to redeclare a universe.
    Also merges the universe context in the local constraint structures
    and not only in the graph. *)
let merge ?loc ~sideff rigid uctx uctx' =
  let levels = PConstraints.ContextSet.levels uctx' in
  let local = PConstraints.ContextSet.append uctx' uctx.local in
  let declare g =
    Level.Set.fold (fun u g ->
        try UGraph.add_universe ~strict:false u g
        with UGraph.AlreadyDeclared when sideff -> g)
      levels g
  in
  let names =
    let fold u accu =
      let update = function
        | None -> Some { uname = None; uloc = loc }
        | Some info -> match info.uloc with
          | None -> Some { info with uloc = loc }
          | Some _ -> Some info
      in
      Level.Map.update u update accu
    in
    (fst uctx.names, (fst (snd uctx.names), Level.Set.fold fold levels (snd (snd uctx.names))))
  in
  let initial = declare uctx.initial_universes in
  let univs = declare uctx.universes in
  let universes = merge_univ_constraints uctx (PConstraints.ContextSet.univ_constraints uctx') univs in
  let uctx =
    match rigid with
    | UnivRigid -> uctx
    | UnivFlexible b ->
      assert (not sideff);
      let uvars' = UnivFlex.add_levels levels ~algebraic:b uctx.univ_variables in
      { uctx with univ_variables = uvars' }
  in
  { uctx with names; local; universes;
              initial_universes = initial }

let merge_sort_variables ?loc ~sideff uctx src qvars csts =
  let sort_variables =
    QVar.Set.fold (fun qv qstate -> QState.add ~check_fresh:(not sideff) ~rigid:false qv qstate)
      qvars
      uctx.sort_variables
  in
  let names =
    let fold u accu =
      let update = function
        | None -> Some { uname = None; uloc = loc }
        | Some info -> match info.uloc with
          | None -> Some { info with uloc = loc }
          | Some _ -> Some info
      in
      QVar.Map.update u update accu
    in
    let qrev = QVar.Set.fold fold qvars (fst (snd uctx.names)) in
    (fst uctx.names, (qrev, snd (snd uctx.names)))
  in
  let sort_variables = QState.merge_constraints (merge_elim_constraints src uctx csts) sort_variables in
  { uctx with sort_variables; names }

let merge_sort_context ?loc ~sideff rigid src uctx ((qvars,levels),csts) =
  let uctx = merge_sort_variables ?loc ~sideff uctx src qvars (PConstraints.qualities csts) in
  merge ?loc ~sideff rigid uctx (levels,csts)

let demote_global_univs (lvl_set, univ_csts) uctx =
  let (local_univs, local_constraints) = uctx.local in
  let local_univs = Level.Set.diff local_univs lvl_set in
  let univ_variables = Level.Set.fold UnivFlex.remove lvl_set uctx.univ_variables in
  let update_ugraph g =
    let g = Level.Set.fold (fun u g ->
        try UGraph.add_universe u ~strict:true g
        with UGraph.AlreadyDeclared -> g)
        lvl_set
        g
    in
    UGraph.merge_constraints univ_csts g
  in
  let initial_universes = update_ugraph uctx.initial_universes in
  let universes = update_ugraph uctx.universes in
  { uctx with local = (local_univs, local_constraints); univ_variables; universes; initial_universes }

let demote_global_univ_entry entry uctx = match entry with
| Monomorphic_entry ucst ->
  demote_global_univs ucst uctx
| Polymorphic_entry _ -> uctx

(* Check bug_4363 bug_6323 bug_3539 and success/rewrite lemma l1
   for quick feedback when changing this code *)
let emit_side_effects eff u =
  let uctx = Safe_typing.universes_of_private eff in
  demote_global_univs uctx u

let merge_seff uctx uctx' =
  let levels = PConstraints.ContextSet.levels uctx' in
  let declare g =
    Level.Set.fold (fun u g ->
        try UGraph.add_universe ~strict:false u g
        with UGraph.AlreadyDeclared -> g)
      levels g
  in
  let initial_universes = declare uctx.initial_universes in
  let univs = declare uctx.universes in
  let universes = merge_univ_constraints uctx (PConstraints.ContextSet.univ_constraints uctx') univs in
  { uctx with universes; initial_universes }

let update_sigma_univs uctx univs =
  let eunivs =
    { uctx with
      initial_universes = univs;
      universes = univs }
  in
  merge_seff eunivs eunivs.local

let add_qnames ?loc s l ((qnames,unames), (qnames_rev,unames_rev)) =
  if Id.Map.mem s qnames
  then user_err ?loc
      Pp.(str "Quality " ++ Id.print s ++ str" already bound.");
  ((Id.Map.add s l qnames, unames),
   (QVar.Map.add l { uname = Some s; uloc = loc } qnames_rev, unames_rev))

let add_names ?loc s l ((qnames,unames), (qnames_rev,unames_rev)) =
  if UNameMap.mem s unames
  then user_err ?loc
      Pp.(str "Universe " ++ Id.print s ++ str" already bound.");
  ((qnames,UNameMap.add s l unames),
   (qnames_rev, Level.Map.add l { uname = Some s; uloc = loc } unames_rev))

let add_qloc l loc (names, (qnames_rev,unames_rev) as orig) =
  match loc with
  | None -> orig
  | Some _ -> (names, (QVar.Map.add l { uname = None; uloc = loc } qnames_rev, unames_rev))

let add_loc l loc (names, (qnames_rev,unames_rev) as orig) =
  match loc with
  | None -> orig
  | Some _ -> (names, (qnames_rev, Level.Map.add l { uname = None; uloc = loc } unames_rev))

let add_universe ?loc name strict uctx u =
  let initial_universes = UGraph.add_universe ~strict u uctx.initial_universes in
  let universes = UGraph.add_universe ~strict u uctx.universes in
  let local = PConstraints.ContextSet.add_level u uctx.local in
  let names =
    match name with
    | Some n -> add_names ?loc n u uctx.names
    | None -> add_loc u loc uctx.names
  in
  { uctx with names; local; initial_universes; universes }

let new_sort_variable ?loc ?name uctx =
  let q = UnivGen.fresh_sort_quality () in
  (* don't need to check_fresh as it's guaranteed new *)
  let sort_variables = QState.add ~check_fresh:false ~rigid:(Option.has_some name)
      q uctx.sort_variables
  in
  let names = match name with
    | Some n -> add_qnames ?loc n q uctx.names
    | None -> add_qloc q loc uctx.names
  in
  { uctx with sort_variables; names }, q

let new_univ_variable ?loc rigid name uctx =
  let u = UnivGen.fresh_level () in
  let uctx =
    match rigid with
    | UnivRigid -> uctx
    | UnivFlexible algebraic ->
      let univ_variables = UnivFlex.add u ~algebraic uctx.univ_variables in
      { uctx with univ_variables }
  in
  let uctx = add_universe ?loc name false uctx u in
  uctx, u

let add_forgotten_univ uctx u = add_universe None true uctx u

let make_with_initial_binders ~qualities univs binders =
  let uctx = make ~qualities univs in
  List.fold_left
    (fun uctx { CAst.loc; v = id } ->
       fst (new_univ_variable ?loc univ_rigid (Some id) uctx))
    uctx binders

let from_env ?(binders=[]) env =
  make_with_initial_binders
    ~qualities:(Environ.qualities env)
    (Environ.universes env)
    binders

let make_nonalgebraic_variable uctx u =
  { uctx with univ_variables = UnivFlex.make_nonalgebraic_variable uctx.univ_variables u }

let make_flexible_nonalgebraic uctx =
  { uctx with univ_variables = UnivFlex.make_all_undefined_nonalgebraic uctx.univ_variables }

let subst_univs_context_with_def def usubst (uctx, (elim_csts,univ_csts)) =
  (Level.Set.diff uctx def, PConstraints.make elim_csts @@
                              UnivSubst.subst_univs_constraints usubst univ_csts)

let normalize_univ_variables uctx =
  let normalized_variables, def, subst =
    UnivFlex.normalize_univ_variables uctx.univ_variables
  in
  let uctx_local = subst_univs_context_with_def def subst uctx.local in
  let univs = UGraph.merge_constraints (snd (snd uctx_local)) uctx.initial_universes in
  { uctx with
    local = uctx_local;
    univ_variables = normalized_variables;
    universes = univs }

let normalize_quality_variables uctx =
  let (lvls, (elim_cstrs, lvl_cstrs)) = uctx.local in
  let elim_cstrs = QState.normalize_elim_constraints uctx.sort_variables elim_cstrs in
  { uctx with local = (lvls, (elim_cstrs, lvl_cstrs)) }

let normalize_variables uctx =
  let uctx = normalize_univ_variables uctx in
  normalize_quality_variables uctx

let fix_undefined_variables uctx =
  { uctx with univ_variables = UnivFlex.fix_undefined_variables uctx.univ_variables }

let collapse_above_prop_sort_variables ~to_prop uctx =
  let sorts = QState.collapse_above_prop ~to_prop uctx.sort_variables in
  normalize_quality_variables { uctx with sort_variables = sorts }

let collapse_sort_variables ?except uctx =
  let sorts = QState.collapse ?except uctx.sort_variables in
  normalize_quality_variables { uctx with sort_variables = sorts }

let minimize uctx =
  let open UnivMinim in
  let (vars', us') =
    normalize_context_set uctx.universes uctx.local uctx.univ_variables
      uctx.minim_extra
  in
  if PConstraints.ContextSet.equal us' uctx.local then uctx
  else
    let universes = UGraph.merge_constraints (snd (snd us')) uctx.initial_universes in
      { names = uctx.names;
        local = us';
        univ_variables = vars';
        sort_variables = uctx.sort_variables;
        universes = universes;
        initial_universes = uctx.initial_universes;
        minim_extra = UnivMinim.empty_extra; (* weak constraints are consumed *) }

let universe_context_inst_decl decl qvars levels names =
  let leftqs = List.fold_left (fun acc l -> QSet.remove l acc) qvars decl.univdecl_qualities in
  let leftus = List.fold_left (fun acc l -> Level.Set.remove l acc) levels decl.univdecl_instance in
  let () =
    let unboundqs = if decl.univdecl_extensible_qualities then QSet.empty else leftqs in
    let unboundus = if decl.univdecl_extensible_instance then Level.Set.empty else leftus in
    if not (QSet.is_empty unboundqs && Level.Set.is_empty unboundus)
    then error_unbound_universes unboundqs unboundus names
  in
  let instq = Array.map_of_list (fun q -> QVar q) decl.univdecl_qualities in
  let instu = Array.of_list decl.univdecl_instance in
  let inst = Instance.of_array (instq,instu) in
  inst

let check_univ_decl_rev uctx decl =
  let levels, (elim_csts,univ_csts as csts) = uctx.local in
  let qvars = QState.undefined uctx.sort_variables in
  let inst = universe_context_inst_decl decl qvars levels uctx.names in
  let nas = compute_instance_binders uctx inst in
  let () = check_implication uctx csts (univ_decl_csts decl)
  in
  let uctx = fix_undefined_variables uctx in
  let uctx, univ_csts =
    if decl.univdecl_extensible_constraints
    then uctx, univ_csts
    else restrict_univ_constraints uctx decl.univdecl_univ_constraints,
         univ_csts
  in
  let uctx, elim_csts =
    if decl.univdecl_extensible_constraints
    then uctx, elim_csts
    else restrict_elim_constraints QGraph.Rigid uctx decl.univdecl_elim_constraints,
         elim_csts
  in
  let uctx' = UContext.make nas (inst, (elim_csts,univ_csts)) in
  uctx, uctx'

let check_uctx_impl ~fail uctx uctx' =
  let levels, (elim_csts,univ_csts) = uctx'.local in
  let qvars_diff =
    QVar.Set.diff
      (QState.undefined uctx'.sort_variables)
      (QState.undefined uctx.sort_variables)
  in
  let levels_diff = Level.Set.diff levels (fst uctx.local) in
  let () = if not @@ (QVar.Set.is_empty qvars_diff && Level.Set.is_empty levels_diff) then
    error_unbound_universes qvars_diff levels_diff uctx'.names
  in
  let () =
    let grext = ugraph uctx in
    let cstrs' = UnivConstraints.filter (fun c -> not (UGraph.check_constraint grext c)) univ_csts in
    if UnivConstraints.is_empty cstrs' then ()
    else fail (UnivConstraints.pr (pr_uctx_level uctx) cstrs')
  in
  let () =
    let grext = elim_graph uctx in
    let cstrs' = ElimConstraints.filter (fun c -> not (QGraph.check_constraint grext c)) elim_csts in
    if ElimConstraints.is_empty cstrs' then ()
    else fail (ElimConstraints.pr (pr_uctx_qvar uctx) cstrs')
  in
  ()


(* XXX print above_prop too *)
let pr_weak prl {minim_extra={UnivMinim.weak_constraints=weak; above_prop}} =
  let open Pp in
  v 0 (
    prlist_with_sep cut (fun (u,v) -> h (prl u ++ str " ~ " ++ prl v)) (UPairSet.elements weak)
    ++ if UPairSet.is_empty weak || Level.Set.is_empty above_prop then mt() else cut () ++
    prlist_with_sep cut (fun u -> h (str "Prop <= " ++ prl u)) (Level.Set.elements above_prop))

let pr_sort_opt_subst uctx = QState.pr (qualid_of_qvar_names uctx.names) uctx.sort_variables

let pr ctx =
  let open Pp in
  let prl = pr_uctx_level ctx in
  let prq = pr_uctx_qvar ctx in
  if is_empty ctx then mt ()
  else
    v 0
      (str"UNIVERSES:"++brk(0,1)++
       h (PConstraints.ContextSet.pr prq prl (context_set ctx)) ++ fnl () ++
       UnivFlex.pr prl (subst ctx) ++ fnl() ++
       str"SORTS:"++brk(0,1)++
       h (pr_sort_opt_subst ctx) ++ fnl() ++
       str "WEAK CONSTRAINTS:"++brk(0,1)++
       h (pr_weak prl ctx) ++ fnl ())

module Internal =
struct

let reboot env uctx =
  let uctx_global = from_env env in
  { uctx_global with univ_variables = uctx.univ_variables; sort_variables = uctx.sort_variables }

end
