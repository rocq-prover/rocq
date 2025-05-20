(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Univ
open UnivSubst
open InferCumulativity

let _debug_minim, debug = CDebug.create_full ~name:"univMinim" ()
let _debug_minim_each, debug_each = CDebug.create_full ~name:"univMinim_each" ()
let _debug_minim_each, debug_graph = CDebug.create_full ~name:"univMinim_graph" ()
let switch_minim, _ = CDebug.create_full ~name:"switchminim" ()
let () = CDebug.set_flag switch_minim true

(* To disallow minimization to Set *)
let { Goptions.get = get_set_minimization } =
  Goptions.declare_bool_option_and_ref
    ~key:["Universe";"Minimization";"ToSet"]
    ~value:true
    ()

(** Simplification *)

(** Precondition: flexible <= ctx *)

let variance_info u flex (variances : InferCumulativity.variances) =
  let open UVars.Variance in
  match Level.Map.find_opt u variances with
  | None -> if Level.Set.mem u flex then Irrelevant, Irrelevant, Irrelevant, None else Invariant, Invariant, Invariant, None
  | Some occs ->
    let termv, typev, principal = term_type_variances occs in
    Option.default Irrelevant termv, Option.default Irrelevant typev, Option.default Irrelevant principal, occs.infer_under_impred_qvars

let _warn_not_minimizable u =
  Feedback.msg_notice Pp.(str"Universe " ++ Level.raw_pr u ++ str" is not mimimizable as its lower bound \
       is not expressible in terms of other universes")

let update_variance (variances : InferCumulativity.variances) l l' =
  match Level.Map.find_opt l variances with
  | None -> variances
  | Some loccs ->
    let upd = function None -> None | Some l'occs -> Some (sup_occs loccs l'occs) in
    Level.Map.update l' upd variances

let update_variances (variances : InferCumulativity.variances) l ls =
  match Level.Map.find_opt l variances with
  | None -> variances
  | Some loccs ->
    let update_one l' variances =
      let upd = function None -> None | Some l'occs -> Some (sup_occs loccs l'occs) in
      Level.Map.update l' upd variances
    in
    Level.Set.fold update_one ls variances

let set_variance (variances : InferCumulativity.variances) l v =
  Level.Map.add l v variances

let sup_variances (variances : InferCumulativity.variances) ls =
  let fold l acc =
    match Level.Map.find_opt l variances with
    | None -> acc
    | Some occs -> sup_occs occs acc
  in
  Level.Set.fold fold ls InferCumulativity.default_occ

let update_univ_subst (ctx, flex, variances, graph) subst =
  let flex = List.fold_right (fun (l, u) -> Level.Set.remove l) subst flex in
  let ctx = List.fold_right (fun (l, _) -> Level.Set.remove l) subst ctx in
  let variances = List.fold_right (fun (l, u) variances -> Level.Map.remove l (update_variances variances l (Univ.Universe.levels u))) subst variances in
  (ctx, flex, variances, graph)

let pr_subst =
  let open Pp in
  let pr_subst (l, u) = Level.raw_pr l ++ str " := " ++ Universe.pr Level.raw_pr u in
  prlist_with_sep spc pr_subst

let subst_of_equivalences us =
  List.filter_map (fun (l, le) ->
    if Level.Set.mem l us then Some (l, Universe.of_expr le)
    else None)

let instantiate_variable l (b : Universe.t) (ctx, flex, variances, graph) =
  debug Pp.(fun () -> str"Instantiating " ++ Level.raw_pr l ++ str " with " ++ Universe.pr Level.raw_pr b);
  debug Pp.(fun () -> str"Context: " ++ Level.Set.pr Level.raw_pr ctx);
  debug_graph Pp.(fun () -> str"Model: " ++ UGraph.pr_model ~local:true graph);
  let graph, equivs = UGraph.set l b graph in
  let subst = subst_of_equivalences flex equivs in
  debug Pp.(fun () -> str "Set affected also: " ++ pr_subst subst);
  debug_graph Pp.(fun () -> str"Model after set: " ++ UGraph.pr_model ~local:true graph);
  update_univ_subst (ctx, flex, variances, graph) ((l, b) :: subst)

let update_equivs_bound (_, us, _, _ as acc) l u equivs =
  update_univ_subst acc ((l, u) :: subst_of_equivalences us equivs)

let simplify_variables solve_flexibles partial ctx flex variances graph =
  let open UVars.Variance in
  debug_each Pp.(fun () -> str"Simplifying variables with " ++ (if partial then str"partial" else str"non-partial") ++ str" information about the definition");
  let minimize u (ctx, flex, variances, graph) =
    match UGraph.minimize u graph with
    | HasSubst (graph, equivs, lbound) ->
      debug_each Pp.(fun () -> str"Minimizing " ++ Level.raw_pr u ++ str" resulted in lbound: " ++ Universe.pr Level.raw_pr lbound);
      update_equivs_bound (ctx, flex, variances, graph) u lbound equivs
    | NoBound | CannotSimplify -> (ctx, flex, variances, graph)
  in
  let collapse_to_zero u acc =
    try instantiate_variable u Universe.type0 acc
    with UGraph.InconsistentEquality | UGraph.OccurCheck -> acc
  in
  let maximize u (ctx, flex, variances, graph as acc) =
    match UGraph.maximize u graph with
    | HasSubst (graph, equivs, ubound) ->
      debug_each Pp.(fun () -> str"Maximizing " ++ Level.raw_pr u ++ str" resulted in ubound: " ++ Universe.pr Level.raw_pr ubound);
      update_equivs_bound (ctx, flex, variances, graph) u ubound equivs
    | NoBound | CannotSimplify -> acc
  in
  let arbitrary ~allow_collapse u (ctx, flex, variances, graph as acc) =
    match UGraph.minimize u graph with
      | HasSubst (graph, equivs, lbound) ->
        debug_each Pp.(fun () -> str"Minimizing " ++ Level.raw_pr u ++ str" resulted in lbound: " ++ Universe.pr Level.raw_pr lbound);
        update_equivs_bound (ctx, flex, variances, graph) u lbound equivs
      | NoBound -> (* Not bounded and not appearing anywhere: can collapse *)
        if allow_collapse then collapse_to_zero u acc
        else maximize u acc
      | CannotSimplify -> maximize u acc
  in
  let simplify_impred u acc = function
    | None -> (* Unused variable *) acc
    | Some UVars.Predicative -> (* Used in some predicative contexts *) acc
    | Some (UVars.Impredicative qs) ->
      if not partial && Sorts.QVar.Set.is_empty qs then collapse_to_zero u acc
      else acc
  in
  let simplify_min u (ctx, flex, variances, graph as acc) =
    (* u is an undefined flexible variable, lookup its variance information *)
    let term_variance, type_variance, typing_variance, impred = variance_info u flex variances in
    if typing_variance == Irrelevant then
      (* The universe does not occur relevantly in the principal type of the expressions where it appears *)
      match type_variance with
      | Irrelevant -> arbitrary ~allow_collapse:true u acc
      | Covariant -> minimize u acc
      | Contravariant -> acc (* Do not maximize at first, as it would break the template hacks with max (0, ...) *)
      | Invariant -> acc
    else
      match typing_variance with
      | Covariant when not partial -> minimize u acc
      | Contravariant when not partial ->
        (* Do not maximize at first, as it would break template hacks with max(0,_) *)
        simplify_impred u acc impred
      | _ -> simplify_impred u acc impred

  in
  let (_, flex, _, _ as acc) = Level.Set.fold simplify_min flex (ctx, flex, variances, graph) in
  let simplify_max u (ctx, flex, variances, graph as acc) =
    (* u is an undefined flexible variable, lookup its variance information *)
    let term_variance, type_variance, typing_variance, _impred_qvars = variance_info u flex variances in
    if typing_variance == Irrelevant && type_variance == Irrelevant then
      maximize u acc
    else
      let open UVars.Variance in
      match term_variance, type_variance, typing_variance with
      | (Covariant | Irrelevant), Contravariant, (Irrelevant | Contravariant) when not partial -> maximize u acc
      | _, _, _ -> acc
  in
  let (_, flex, _, _ as acc) = Level.Set.fold simplify_max flex acc in
  let simplify_arbitrary ~allow_collapse u (ctx, flex, variances, graph as acc) =
    (* u is an undefined flexible variable, lookup its variance information *)
    let term_variance, type_variance, typing_variance, _impred_qvars = variance_info u flex variances in
    debug_each Pp.(fun () -> str"Simplifying flexible " ++ Level.raw_pr u ++ str" arbitrarily, type variance: " ++ UVars.Variance.pr type_variance ++ 
      str " typing_variance: " ++ UVars.Variance.pr typing_variance);
    match type_variance with 
    | Irrelevant -> arbitrary ~allow_collapse:true u acc
    | Covariant -> minimize u acc
    | Contravariant -> maximize u acc
    | Invariant -> acc
  in
  if solve_flexibles then
    let fold_arbitrary u (ctx, flex, variances, graph as acc) =
      if not (Level.Set.mem u flex) then acc
      else simplify_arbitrary ~allow_collapse:(get_set_minimization ()) u acc
    in
    Level.Set.fold fold_arbitrary flex acc
  else acc

module UPairs = OrderedType.UnorderedPair(Universe)
module UPairSet = Set.Make (UPairs)

type extra = {
  weak_constraints : UPairSet.t;
  above_prop : Level.Set.t;
}

let empty_extra = {
  weak_constraints = UPairSet.empty;
  above_prop = Level.Set.empty;
}

let extra_union a b = {
  weak_constraints = UPairSet.union a.weak_constraints b.weak_constraints;
  above_prop = Level.Set.union a.above_prop b.above_prop;
}

(* let pr_universe_set prl s = 
  let open Pp in
  str "{" ++ LevelExpr.Set.fold (fun lk acc -> LevelExpr.pr prl lk ++ str", " ++ acc) s (mt()) ++ str "}"  *)

let pr_universe_set prl s = 
  let open Pp in
  str "{" ++ Universe.Set.fold (fun lk acc -> Universe.pr prl lk ++ str", " ++ acc) s (mt()) ++ str "}" 
  
let _pr_partition prl m =
  let open Pp in
  prlist_with_sep spc (fun s -> pr_universe_set prl s ++ fnl ()) m

let pr_substitution prl m =
  let open Pp in
  prlist_with_sep spc (fun (l, u) -> prl l ++ str" := " ++ Universe.pr prl u ++ fnl ()) (Level.Map.bindings m)
  
(** Turn max(l, l') <= u constraints into { l <= u, l' <= u } constraints *)
let decompose_constraints cstrs =
  let fold (l, d, r as cstr) acc =
    match d with
    | Eq -> Constraints.add cstr acc
    | Le ->
      match Universe.repr l with
      | [] -> assert false
      | [_] -> Constraints.add cstr acc
      | l -> List.fold_left (fun acc le -> enforce (Universe.of_list [le]) d r acc) acc l
  in Constraints.fold fold cstrs Constraints.empty

let simplify_cstr (l, d, r) =
  (Universe.unrepr (Universe.repr l), d, Universe.unrepr (Universe.repr r))

let constraints_of_substitution substitution cstrs =
  Level.Map.fold (fun l u cstrs ->
    Constraints.add (Universe.make l, Eq, u) cstrs) substitution cstrs

let new_minimize_weak_pre g weak smallles =
  UPairSet.fold (fun (u,v) smallles ->
    let norm = Universe.subst_fn (level_subst_of (UGraph.normalize g)) in
    let u = norm u and v = norm v in
    if (Universe.is_type0 u || Universe.is_type0 v) then begin
      if get_set_minimization() then begin
        if Universe.is_type0 u then (Constraints.add (u,Le,v) smallles)
        else (Constraints.add (v,Le,u) smallles)
      end else smallles
    end else smallles)
    weak smallles

let new_minimize_weak ctx flex weak (g, variances) =
  UPairSet.fold (fun (u,v) (ctx, flex, variances, g as acc) ->
    let norm = Universe.subst_fn (level_subst_of (UGraph.normalize g)) in
    let u = norm u and v = norm v in
    if (Universe.is_type0 u || Universe.is_type0 v) then acc
    else
      let set_to a b =
        debug Pp.(fun () -> str"Minimize_weak: setting " ++ Level.raw_pr a ++ str" to " ++ Universe.pr Level.raw_pr b);
        let levels = Universe.levels b in
        let sup_variances = sup_variances variances (Level.Set.add a levels) in
        match InferCumulativity.term_type_variances sup_variances with
        | (None | Some UVars.Variance.Irrelevant), (None | Some UVars.Variance.Irrelevant),
          (None | Some Irrelevant) -> (* Irrelevant *)
          let variances =
            Level.Set.fold (fun bl variances -> set_variance variances bl sup_variances) levels variances
          in
          (try let g, equivs = UGraph.set a b g in
            update_equivs_bound (ctx, flex, variances, g) a b equivs
          with UGraph.InconsistentEquality | UGraph.OccurCheck -> acc)
        | _, _, _ -> (* One universe is not irrelevant *)
          (ctx, flex, variances, g)
      in
      let check_le a b = UGraph.check_constraint g (a,Le,b) in
      if check_le u v || check_le v u
      then acc
      else match Universe.level u with
      | Some u when Level.Set.mem u flex -> set_to u v
      | _ ->
        match Universe.level v with
        | Some v when Level.Set.mem v flex -> set_to v u
        | _ -> acc)
    weak (ctx, flex, variances, g)



let levels_constraints_of_substitution substitution ctx =
  Level.Map.fold (fun l u (levels, cstrs) ->
    Level.Set.add l levels,
    Constraints.add (Universe.make l, Eq, u) cstrs) substitution ctx

let graph_ctx g = 
  let (levels, cstrs, eqs) = UGraph.constraints_of_universes ~only_local:true g in
  levels_constraints_of_substitution eqs (levels, cstrs)

let normalize_context_set ~solve_flexibles ~variances ~partial g ~local_variables ~flexible_variables ?binders {weak_constraints=weak;above_prop} =
  let prl = UnivNames.pr_level_with_global_universes ?binders in
  let gctx = graph_ctx g in
  debug Pp.(fun () -> str "Minimizing context: " ++ ContextSet.pr prl gctx ++ spc () ++
    str"Local variables: " ++ Level.Set.pr Level.raw_pr local_variables ++ fnl () ++
    str"Flexible variables: " ++ Level.Set.pr Level.raw_pr flexible_variables ++ fnl () ++
    str"Variances: " ++ pr_variances prl variances ++ fnl () ++
    str"Weak constraints " ++
    prlist_with_sep spc (fun (u,v) -> Universe.pr Level.raw_pr u ++ str" ~ " ++ Universe.pr Level.raw_pr v)
     (UPairSet.elements weak) ++
     (if partial then str"In partial mode" else str"In non-partial mode") );
  debug_graph Pp.(fun () ->
     str"Graph: " ++ UGraph.pr_model g);
  if CDebug.get_flag _debug_minim then
    if not (Level.Set.is_empty local_variables) && InferCumulativity.is_empty_variances variances then
      Feedback.msg_debug Pp.(str"normalize_context_set called with empty variance information");
  let (ctx, csts) = gctx in
  (* Keep the Prop/Set <= i constraints separate for minimization *)
  let csts = decompose_constraints csts in
  let smallles, csts =
    Constraints.partition (fun (l,d,r) -> d == Le && Universe.is_type0 l) csts
  in
  (* Process weak constraints: when one side is flexible and the 2
     universes are unrelated unify them. *)
  let smallles = new_minimize_weak_pre g weak smallles in
  let smallles = if get_set_minimization () then
      Constraints.filter (fun (l,d,r) -> match Universe.level r with Some r -> Level.Set.mem r flexible_variables | None -> false) smallles
    else Constraints.empty (* constraints Set <= u may be dropped *)
  in
  let smallles = if get_set_minimization() then
      let fold u accu = if Level.Set.mem u flexible_variables then enforce_leq Universe.type0 (Universe.make u) accu else accu in
      Level.Set.fold fold above_prop smallles
    else smallles
  in
  let graph = g in
  (* debug Pp.(fun () -> str "Local graph: " ++ UGraph.pr_model graph); *)
  let locals, cstrs, lsubst = UGraph.constraints_of_universes ~only_local:true g in
  (* debug Pp.(fun () -> str "Local universes: " ++ pr_universe_context_set prl (locals, cstrs)); *)
  (* debug Pp.(fun () -> str "New universe context: " ++ pr_universe_context_set prl (ctx, cstrs)); *)
  debug Pp.(fun () -> str "Substitution: " ++ pr_substitution prl lsubst);
(* Ignore constraints from lbound:Set *)
  let noneqs =
    Constraints.filter
      (fun (l,d,r) -> not (d == Le && Universe.is_type0 l))
      cstrs
  in
  (* Put back constraints [Set <= u] from type inference *)
  let noneqs = Constraints.union noneqs smallles in
  (* Noneqs is now in canonical form w.r.t. equality constraints,
     and contains only inequality constraints. *)
  let noneqs =
    let fold (u,d,v) noneqs =
      if Universe.equal u v then noneqs
      else Constraints.add (u,d,v) noneqs
    in
    Constraints.fold fold noneqs Constraints.empty
  in
  (* Now we construct the instantiation of each variable. *)
  debug Pp.(fun () -> str "Starting minimization with: " ++ ContextSet.pr prl (ctx, noneqs) ++ spc () ++
    Level.Set.pr Level.raw_pr flexible_variables ++ spc () ++
    if solve_flexibles then str "solving all flexibles" else str" solving flexibles respecting variances information");
  let ctx', flex, variances, noneqs, graph =
    let smalllesu = Constraints.fold (fun (l, d, r) acc ->
      match Universe.level r with Some r -> Level.Set.add r acc | None -> acc) smallles Level.Set.empty in
    (* debug Pp.(fun () -> str"Model before removal: " ++ UGraph.pr_model graph); *)
    let graph = Level.Set.fold (fun l graph ->
      if not (Level.Set.mem l smalllesu) then
        (debug Pp.(fun () -> str"Removing " ++ Level.raw_pr l ++ str" -> Set constraints");
          UGraph.remove_set_clauses l graph)
      else graph)
      flexible_variables graph
    in
    (* debug Pp.(fun () -> str"Model after removal: " ++ UGraph.pr_model graph); *)
    let ctx', flex, variances, graph = simplify_variables solve_flexibles partial ctx flexible_variables variances graph in
    debug_graph Pp.(fun () -> str"Model after simplification: " ++ UGraph.pr_model graph ++ fnl () ++ Level.Set.pr Level.raw_pr flex);
    let ctx', us, variances, graph = new_minimize_weak ctx' flex weak (graph, variances) in
    let locals, cstrs, substitution = UGraph.constraints_of_universes ~only_local:true graph in
    let cstrs = constraints_of_substitution substitution cstrs in
    let cstrs =
      Constraints.filter
        (fun (l,d,r) -> not (d == Le && Universe.is_type0 l))
        cstrs
    in
    let cstrs = Constraints.union smallles cstrs in
    ctx', us, variances, cstrs, graph
  in
  let cstrs = Constraints.filter (fun (l, d, r) -> not (d == Le && Universe.is_type0 l)) noneqs in
  let ctx = (ctx', cstrs) in
  debug Pp.(fun () -> str "After minimization: " ++ ContextSet.pr prl ctx ++ fnl () ++
    Level.Set.pr Level.raw_pr flex ++ fnl () ++
    str"VARIANCES: " ++ InferCumulativity.pr_variances Level.raw_pr variances);
  (flex, variances), ctx
