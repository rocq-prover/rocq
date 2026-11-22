(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Univ
open InferCumulativity

let _debug_minim, debug = CDebug.create_full ~name:"univMinim" ()
let _debug_minim_each, debug_each = CDebug.create_full ~name:"univMinim_each" ()
let _debug_minim_each, debug_graph = CDebug.create_full ~name:"univMinim_graph" ()

let disable_solve_term, _ = CDebug.create_full ~name:"minim-solve-term" ()
let disable_lifted_from_binder, _ = CDebug.create_full ~name:"minim-no-lifted" ()
let disable_folded_check, _ = CDebug.create_full ~name:"minim-no-folded-check" ()

(* To disallow minimization to Set *)
let { Goptions.get = get_set_minimization } =
  Goptions.declare_bool_option_and_ref
    ~key:["Universe";"Minimization";"ToSet"]
    ~value:true
    ()

(* To also minimize the flexible universes without upper bound whose lower bound is an invariant
   level, whatever their own variance, and the flexible universes not occurring in the type
   (see [simplify_variables]) *)
let { Goptions.get = get_compat_minimization } =
  Goptions.declare_bool_option_and_ref
    ~key:["Universe";"Minimization";"Compat"]
    ~value:false
    ()

(** Simplification *)

let variance_info u flex (variances : InferCumulativity.variances) =
  let open UVars.Variance in
  match Level.Map.find_opt u variances with
  | None -> if Level.Set.mem u flex then Irrelevant, Irrelevant, Irrelevant, None else Invariant, Invariant, Invariant, None
  | Some occs ->
    let termv, typev, principal = term_type_variances occs in
    Option.default Irrelevant termv, Option.default Irrelevant typev, Option.default Irrelevant principal, occs.infer_under_impred_qvars

(* [u] occurs in the type of the declaration or in its binders, possibly irrelevantly, e.g. a
   universe the inference reduces away (see [InferCumulativity.Inf.add_irrelevant_type_occurrences]) *)
let occurs_in_type u (variances : InferCumulativity.variances) =
  match Level.Map.find_opt u variances with
  | None -> false
  | Some { InferCumulativity.infer_binders = (_, (b, _)); infer_topfix_binders = (_, (fb, _));
           infer_type = (_, t); _ } ->
    Option.has_some b || Option.has_some fb || Option.has_some t

(* [u] occurs relevantly for cumulativity in the type of the declaration, e.g. in the type of a
   binder: setting it to a bound of its choice would make this type less general *)
let in_declared_type u (variances : InferCumulativity.variances) =
  match Level.Map.find_opt u variances with
  | None -> false
  | Some occs ->
    match InferCumulativity.declared_type_cumul_variance occs with
    | None | Some UVars.Variance.Irrelevant -> false
    | Some _ -> true

(* An algebraic universe ([max(a, b)], [l+1]) only replaces [u] where it is safe: where the types
   of the folded subterms in which [u] occurs (see [InferCumulativity.infer_folded]) are covariant
   in [u], e.g. [Proper@{max(a,b)} R m : Type@{max(a,b)}]. Unification copies such subterms into
   holes, checking their types by cumulativity: elsewhere, e.g. in [f@{max(a,b)} x :
   R@{max(a,b)}] for an inductive [R] invariant in its universe, the universe of the hole would have to be
   equal to [max(a, b)], an upper bound which an independent universe cannot satisfy. A single
   level is allowed anywhere: the hole gets a copy of it. *)
let closed_last_resort = ref false

let algebraic_bound_allowed u bound (variances : InferCumulativity.variances) =
  !closed_last_resort || CDebug.get_flag disable_folded_check || Option.has_some (Universe.level bound) ||
  match Level.Map.find_opt u variances with
  | None -> true
  | Some occs ->
    match occs.InferCumulativity.infer_folded with
    | None | Some (UVars.Variance.Irrelevant | UVars.Variance.Covariant) -> true
    | Some (UVars.Variance.Invariant | UVars.Variance.Contravariant) ->
      debug Pp.(fun () -> str"Not setting " ++ Level.raw_pr u ++ str" to the algebraic " ++ Universe.pr Level.raw_pr bound ++
        str": its folded occurrences are not covariant");
      false

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

let update_univ_subst (flex, variances, graph) subst =
  let flex = List.fold_right (fun (l, u) -> Level.Set.remove l) subst flex in
  let variances = List.fold_right (fun (l, u) variances -> Level.Map.remove l (update_variances variances l (Univ.Universe.levels u))) subst variances in
  (flex, variances, graph)

let pr_subst =
  let open Pp in
  let pr_subst (l, u) = Level.raw_pr l ++ str " := " ++ Universe.pr Level.raw_pr u in
  prlist_with_sep spc pr_subst

let subst_of_equivalences us =
  List.filter_map (fun (l, le) ->
    if Level.Set.mem l us then Some (l, Universe.of_expr le)
    else None)

let instantiate_variable l (b : Universe.t) (flex, variances, graph) =
  debug Pp.(fun () -> str"Instantiating " ++ Level.raw_pr l ++ str " with " ++ Universe.pr Level.raw_pr b);
  debug_graph Pp.(fun () -> str"Model: " ++ UGraph.pr_model ~local:true graph);
  let graph, equivs = UGraph.set l b graph in
  let subst = subst_of_equivalences flex equivs in
  debug Pp.(fun () -> str "Set affected also: " ++ pr_subst subst);
  debug_graph Pp.(fun () -> str"Model after set: " ++ UGraph.pr_model ~local:true graph);
  update_univ_subst (flex, variances, graph) ((l, b) :: subst)

let update_equivs_bound (us, _, _ as acc) l u equivs =
  update_univ_subst acc ((l, u) :: subst_of_equivalences us equivs)

(** [partial]: we have type information only, not term information (i.e. Axiom, Definition/Lemma type only) *)
let simplify_variables solve_flexibles above_prop above_zero internal partial solve_term flex variances graph =
  let open UVars.Variance in
  (* A universe is not set to its lower bound when this would constrain the others (see
     [UGraph.minimize]), unless the universes not declared must all be removed *)
  let require_entailed = not solve_flexibles in
  debug_each Pp.(fun () -> str"Simplifying variables with " ++ (if partial then str"partial" else str"non-partial") ++ str" information about the definition");
  let allowed_instance ~allow_collapse_to_zero u lbound =
    if Universe.is_type0 lbound then
      solve_flexibles || (get_set_minimization () &&
      (allow_collapse_to_zero || Level.Set.mem u above_prop || Level.Set.mem u above_zero))
    else true
  in
  let minimize ~allow_collapse_to_zero u (flex, variances, graph as acc) =
    match UGraph.minimize ~require_entailed u graph with
    | HasSubst (graph, equivs, lbound) ->
      debug_each Pp.(fun () -> str"Minimizing " ++ Level.raw_pr u ++ str" resulted in lbound: " ++ Universe.pr Level.raw_pr lbound);
      if not (allowed_instance ~allow_collapse_to_zero u lbound && algebraic_bound_allowed u lbound variances) then acc
      else update_equivs_bound (flex, variances, graph) u lbound equivs
    | NoBound | CannotSimplify -> acc
  in
  let minimize_not_to_set u (flex, variances, graph as acc) =
    match UGraph.minimize ~require_entailed u graph with
    | HasSubst (graph, equivs, lbound) ->
      if Universe.exists (fun (l, _) -> Level.is_set l) lbound || not (algebraic_bound_allowed u lbound variances) then acc
      else update_equivs_bound (flex, variances, graph) u lbound equivs
    | NoBound | CannotSimplify -> acc
  in
  let collapse_to_zero u acc =
    try instantiate_variable u Universe.type0 acc
    with Loop_checking.NotCanonical -> assert false
       | UGraph.InconsistentEquality | UGraph.OccurCheck -> acc
  in
  (* With [Universe Minimization Compat], a universe is not maximized to a universe which is not
     one of the declaration, e.g. a monomorphic universe of the global environment bounding a
     polymorphic one: this would tie the declaration to it, while the minimization ignoring
     variances never maximized. *)
  let local_bound variances ub =
    not (Universe.exists (fun (l, _) ->
        not (Level.is_set l || Level.Map.mem l variances || Level.Set.mem l flex)) ub)
  in
  let maximize u (_flex, variances, graph0 as acc) =
    match UGraph.maximize u graph0 with
    | HasSubst (_, _, ubound) when get_compat_minimization () && not (local_bound variances ubound) ->
      debug_each Pp.(fun () -> str"Not maximizing " ++ Level.raw_pr u ++ str" to the non-local " ++ Universe.pr Level.raw_pr ubound);
      acc
    | HasSubst (_, _, ubound) when not (algebraic_bound_allowed u ubound variances) -> acc
    | HasSubst (graph, equivs, ubound) ->
      debug_each Pp.(fun () -> str"Maximizing " ++ Level.raw_pr u ++ str" resulted in ubound: " ++ Universe.pr Level.raw_pr ubound);
      update_equivs_bound (flex, variances, graph) u ubound equivs
    | NoBound | CannotSimplify -> acc
  in
  let arbitrary ?(irrelevant=false) ~allow_collapse_to_zero u (flex, variances, graph0 as acc) =
    match UGraph.minimize ~require_entailed u graph0 with
      | HasSubst (graph, equivs, lbound) ->
        debug_each Pp.(fun () -> str"Minimizing " ++ Level.raw_pr u ++ str" resulted in lbound: " ++ Universe.pr Level.raw_pr lbound);
        (* With [Universe Minimization Compat], a universe occurring only in the body of the
           definition, not in its type, is set to [Set] even without [Universe Minimization ToSet]:
           it only remains in the instances of the body, and would otherwise pile up in the
           definitions built on top. Not one occurring in the type, even irrelevantly: the
           unification of this type, unreduced, would make [Set] reach positions where it
           matters. *)
        (* (Not with partial information: the universes of a statement look irrelevant before the
           proof uses them) *)
        (* (Nor when a universe equal to [u], which the substitution sets too, occurs in the
           type) *)
        let body_only l =
          Level.is_set l ||
          if Level.Map.mem l variances then not (occurs_in_type l variances)
          else Level.Set.mem l flex
        in
        let collapse_body_only () =
          irrelevant && not partial && get_compat_minimization () && body_only u &&
          List.for_all (fun (l, (l', _)) -> body_only l && body_only l') equivs
        in
        if (allowed_instance ~allow_collapse_to_zero u lbound || collapse_body_only ())
           && algebraic_bound_allowed u lbound variances then
          update_equivs_bound (flex, variances, graph) u lbound equivs
        else acc
      | NoBound -> (* Not bounded and not appearing anywhere: can collapse *)
        if allow_collapse_to_zero && not (Level.Set.mem u above_prop) then collapse_to_zero u acc
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
  let simplify_min u (flex, variances, graph as acc) =
    (* u is an undefined flexible variable, lookup its variance information *)
    let term_variance, type_variance, typing_variance, impred = variance_info u flex variances in
    debug_each Pp.(fun () -> str"Trying to minimize flexible " ++ Level.raw_pr u ++ str" arbitrarily, type variance: " ++ UVars.Variance.pr type_variance ++
      str " typing_variance: " ++ UVars.Variance.pr typing_variance);
    (* A universe created by a tactic or the unifier, not by the user, is set to its lower bound
       whatever its variances, but only when this does not constrain the other universes, even
       when all the flexibles are solved: it may already be equal to a global universe, e.g. the
       universe of the domain of [list] in [f_equal]. Not with partial information either: the
       universe of the type of [H] in a statement [forall H : x = y, ...] would be set to the
       universe of [x] before the proof relates it to others *)
    let internal_minimized =
      if partial || not (Level.Set.mem u internal) then None else
      match UGraph.minimize ~require_entailed:true u graph with
      | HasSubst (graph, equivs, lbound) when allowed_instance ~allow_collapse_to_zero:false u lbound
                                              && algebraic_bound_allowed u lbound variances ->
        debug_each Pp.(fun () -> str"Minimizing internal " ++ Level.raw_pr u ++ str" to lbound: " ++ Universe.pr Level.raw_pr lbound);
        Some (update_equivs_bound (flex, variances, graph) u lbound equivs)
      | HasSubst _ | NoBound | CannotSimplify -> None
    in
    match internal_minimized with
    | Some acc -> acc
    | None ->
    match typing_variance with
    | Irrelevant ->
      (* The universe does not occur relevantly in the principal type of the expressions where it appears *)
      begin match type_variance with
      | Irrelevant ->
        (* A universe of the type of a binder of the declaration (e.g. [H : P (A@{u})]), not
           affecting the sort of this type, is still part of the type of the declaration: as in
           the minimization ignoring variances, it is only set to its lower bound, and to [Set]
           only with [Universe Minimization ToSet]. *)
        let _, variances, _ = acc in
        if in_declared_type u variances then minimize ~allow_collapse_to_zero:false u acc
        else arbitrary ~irrelevant:true ~allow_collapse_to_zero:true u acc
      | Covariant -> minimize ~allow_collapse_to_zero:false u acc
      | Contravariant -> acc (* Do not maximize at first, as it would break the template hacks with max (0, ...) *)
      | Invariant -> acc
      end
    | Covariant when not partial -> minimize ~allow_collapse_to_zero:false u acc
    | Contravariant when not partial ->
      (* Do not maximize at first, as it would break template hacks with max(0,_) *)
      simplify_impred u acc impred
    | _ ->
      (* Agressive minimization when the universe does not direcly affect the type of the expression. *)
      if not partial && not (CDebug.get_flag disable_solve_term) && type_variance == Irrelevant then
        if solve_term then minimize ~allow_collapse_to_zero:true u acc
        (* The universes not occurring in the type of the declaration, whatever their variances
           in its body, are set to their lower bound: the type does not depend on them, while each
           use would copy them. Not to [Set]: it could still constrain the universes of the type,
           e.g. [u <= max(v, w)] becomes [u <= v] when [w := Set] *)
        else minimize_not_to_set u acc
      else simplify_impred u acc impred
  in
  let (flex, _, _ as acc) = Level.Set.fold simplify_min flex (flex, variances, graph) in
  (* The universes irrelevant to the type of the declaration which cannot be set to their lower
     bounds one at a time, as each substitution would constrain the others, are set to them
     jointly when all their substituted clauses are entailed ([UGraph.substitution_entailed]): the
     constraints on the other universes are then the same, whether they occur in the type or not.
     E.g. the copies [x, y, z] of the universes [a, b, c] of the type, related by
     [x <= max(a, b, c, y', z')], [x' <= max(a, b, c, y, z)], ... with [a <= x], [a <= x'], ...
     All the candidates are tried at once, then the ones with the same lower bound; the
     candidates bounded by another candidate wait for the next round. *)
  let joint_minimize (flex, variances, graph as acc) =
    let candidates = Level.Set.fold (fun u cands ->
        let _, type_variance, _, _ = variance_info u flex variances in
        if type_variance != Irrelevant || in_declared_type u variances then cands else
        match Option.bind (UGraph.lower_bound u graph) Universe.level with
        | Some l when not (Level.is_set l) -> (u, l) :: cands
        | _ -> cands) flex [] in
    let candidates = List.filter (fun (_, l) ->
        not (List.exists (fun (u, _) -> Level.equal u l) candidates)) candidates in
    let apply acc subst =
      List.fold_left (fun (flex, variances, graph as acc) (u, l) ->
          if not (Level.Set.mem u flex) then acc else
          let lbound = Universe.make l in
          match UGraph.set ~entailed:true u lbound graph with
          | graph, equivs ->
            debug_each Pp.(fun () -> str"Minimizing jointly " ++ Level.raw_pr u ++ str" to lbound: " ++ Level.raw_pr l);
            update_equivs_bound (flex, variances, graph) u lbound equivs
          | exception (Loop_checking.NotCanonical | UGraph.InconsistentEquality | UGraph.OccurCheck) -> acc)
        acc subst
    in
    if List.is_empty candidates then None
    else if UGraph.substitution_entailed candidates graph then Some (apply acc candidates)
    else
      let groups = List.fold_left (fun groups (u, l) ->
          Level.Map.update l (fun g -> Some ((u, l) :: Option.default [] g)) groups)
          Level.Map.empty candidates in
      let acc', changed = Level.Map.fold (fun _ group ((_, _, graph as acc), changed) ->
          if UGraph.substitution_entailed group graph then apply acc group, true else acc, changed)
          groups (acc, false) in
      if changed then Some acc' else None
  in
  let rec rounds n acc =
    if Int.equal n 0 then acc else
    match joint_minimize acc with None -> acc | Some acc -> rounds (n - 1) acc
  in
  let (flex, _, _ as acc) =
    if partial then acc else rounds 5 acc
  in
  (* Only to universes of the context of the elaborator (see [UGraph.local_levels]) or [Set], and
     not when [u] occurs in folded subterms (see [algebraic_bound_allowed]): unification copies
     them into holes, e.g. [f@{i a} x : R@{max(i,a)}] for an inductive [R] invariant in its
     universe (test-suite [minimization_folded.v]), where raising [i] to a universe [s] would force
     the universe of a hole to be [max(s, a)]. Covariant occurrences are fine, e.g. a binder
     [H : P@{u u0} A B] with [P@{u u0} A B : Type@{max(u,u0)}], for [u0 <= u].
     The upper bound must be a universe of the parameters itself, i.e. contravariant for typing
     in the binders (see [UnivVariances.binder_typing_pb]): the universes of two parameters are
     merged, e.g. [u0 := u] for [{A : Type@{u}} {B : Type@{u0}}], but the one of a parameter is
     not raised to the one of an index, e.g. the sort of [A] in an inductive [I (A : Type) : Type ->
     Prop] (test-suite [HoTT_coq_089.v]): that would change the arity of the inductive. *)
  let parameter_level variances l =
    Level.is_set l ||
    match Level.Map.find_opt l variances with
    | Some { InferCumulativity.infer_binders = (_, (Some vp, _)); _ } ->
      vp.UVars.VariancePair.typing_variance == UVars.Variance.Contravariant
    | _ -> false
  in
  let maximize_to_own u (_, variances, graph as acc) =
    let folded = match Level.Map.find_opt u variances with
      | Some { InferCumulativity.infer_folded = Some v; _ } ->
        (match v with UVars.Variance.(Irrelevant | Covariant) -> false | _ -> true)
      | _ -> false
    in
    if folded then begin
      debug_each Pp.(fun () -> str"Not maximizing " ++ Level.raw_pr u ++ str": it occurs in folded subterms");
      acc
    end else
    match UGraph.maximize u graph with
    | HasSubst (_, _, ubound) ->
      let own = UGraph.local_levels graph in
      if not (Universe.for_all (fun (l, _) -> parameter_level variances l) ubound) then begin
        debug_each Pp.(fun () -> str"Not maximizing " ++ Level.raw_pr u ++ str" to " ++
          Universe.pr Level.raw_pr ubound ++ str": not a universe of the parameters");
        acc
      end
      else if Universe.for_all (fun (l, _) -> Level.is_set l || Level.Set.mem l own) ubound then maximize u acc
      else begin
        debug_each Pp.(fun () -> str"Not maximizing " ++ Level.raw_pr u ++ str" to the universe " ++
          Universe.pr Level.raw_pr ubound ++ str" of another declaration");
        acc
      end
    | NoBound | CannotSimplify -> acc
  in
  let simplify_max u (flex, variances, graph as acc) =
    (* u is an undefined flexible variable, lookup its variance information *)
    let term_variance, type_variance, typing_variance, _impred_qvars = variance_info u flex variances in
    if typing_variance == Irrelevant && type_variance == Irrelevant && not (in_declared_type u variances) then
      maximize u acc
    else
      let open UVars.Variance in
      match term_variance, type_variance, typing_variance with
      | (Covariant | Irrelevant), Contravariant, (Irrelevant | Contravariant) when not partial ->
        (* E.g. the sort of an arity binder (see [UnivVariances.compute_variances_context]), only
           raised to a universe of the declaration: not to a global one, or one of the section,
           which would tie the declaration to it, e.g. a [Type@{*}] of a [Canonical
           Structure xx@{}] to the universe of the structure *)
        maximize_to_own u acc
      | _, _, _ -> acc
  in
  let (flex, _, _ as acc) = Level.Set.fold simplify_max flex acc in
  (* With [Universe Minimization Compat], a flexible universe that is still undefined, e.g. one
     occurring invariantly, is set to its lower bound, as the minimization ignoring variances did.
     The type loses generality, but the universes made by cumulative instances, only bounded from
     below by the universes of the instances, do not pile up. Its upper bounds do not prevent it:
     the substitution must be entailed ([UGraph.minimize]), so that it does not constrain the
     other universes, e.g. [v := u] with [u <= v <= w] (the universes of the homs and of their
     equalities of the categories of a functor). Setting a universe may make the lower bound of
     another one a single level: the universes are tried again until none is set. *)
  (* Without it, the same holds for a universe lifted from an argument: one occurring neither in the
     binders of the declaration nor non-covariantly in its type, whose only lower bound is a
     universe of the binders. It is made by a cumulative instance of an argument, e.g. [v] in
     [f@{v} c] for an argument [c : C@{u}] of the declaration, which [f@{v}] accepts by
     cumulativity of [C], with [u <= v] only. Keeping it would only
     allow the instances above the universe of the argument, which elaboration never makes, while
     its uses would copy it. *)
  let lifted_from_binder u l variances =
    let in_binders l = match Level.Map.find_opt l variances with
      | None -> false
      | Some { InferCumulativity.infer_binders = (_, (b, _)); infer_topfix_binders = (_, (fb, _)); _ } ->
        Option.has_some b || Option.has_some fb
    in
    let covariant_in_type u = match Level.Map.find_opt u variances with
      | None -> false
      | Some { InferCumulativity.infer_type = (_, t); _ } ->
        match Option.map UVars.VariancePair.cumul_variance t with
        | None | Some (UVars.Variance.Irrelevant | UVars.Variance.Covariant) -> true
        | Some (UVars.Variance.Invariant | UVars.Variance.Contravariant) -> false
    in
    not (in_binders u) && covariant_in_type u && in_binders l
  in
  let (flex, _, _ as acc) =
    let compat = get_compat_minimization () in
    if partial || not (compat || not (CDebug.get_flag disable_lifted_from_binder)) then acc else
    let simplify_unbounded u (flex, variances, graph as acc) =
      if not (Level.Set.mem u flex) then acc
      else match UGraph.minimize ~require_entailed u graph with
        | HasSubst (graph', equivs, lbound) ->
          (* Only when the lower bound is a universe level which occurs invariantly itself, e.g. one
             of the binders of the definition: [u] is identified with it. A universe bounded by [Set],
             by universes the type does not mention, or by an algebraic universe ([max], [l+1]) keeps
             its generality, as it did when instances could only mention levels. *)
          let invariant_level = function
            | [(l, 0)] ->
              not (Level.is_set l) &&
              if compat then
                (* Contravariant for typing: the sort of an arity binder (see
                   [UnivVariances.compute_variances_context]) *)
                let _, typev, typingv, _ = variance_info l flex variances in
                let open UVars.Variance in
                typev == Invariant || typingv == Invariant || typingv == Contravariant
              else lifted_from_binder u l variances
            | _ -> false
          in
          if not (invariant_level (Universe.repr lbound)) then acc
          else begin
            debug_each Pp.(fun () -> str"Minimizing unbounded " ++ Level.raw_pr u ++ str" to lbound: " ++ Universe.pr Level.raw_pr lbound);
            update_equivs_bound (flex, variances, graph') u lbound equivs
          end
        | NoBound | CannotSimplify -> acc
    in
    let rec rounds n (flex, _, _ as acc) =
      let (flex', _, _ as acc') = Level.Set.fold simplify_unbounded flex acc in
      if Int.equal n 0 || Int.equal (Level.Set.cardinal flex') (Level.Set.cardinal flex) then acc'
      else rounds (n - 1) acc'
    in
    rounds 5 acc
  in
  let simplify_arbitrary u (flex, variances, graph as acc) =
    (* u is an undefined flexible variable, lookup its variance information *)
    let term_variance, type_variance, typing_variance, _impred_qvars = variance_info u flex variances in
    debug_each Pp.(fun () -> str"Simplifying flexible " ++ Level.raw_pr u ++ str" arbitrarily, type variance: " ++ UVars.Variance.pr type_variance ++
      str " typing_variance: " ++ UVars.Variance.pr typing_variance);
    match type_variance with
    | Irrelevant -> arbitrary ~allow_collapse_to_zero:true u acc
    | Covariant -> minimize ~allow_collapse_to_zero:true u acc
    | Contravariant -> maximize_to_own u acc
    | Invariant ->
      (* The universe declaration is closed: the universes it does not declare cannot stay, even
         when they occur invariantly in the type, and are set to their lower bound if it is not
         [Set]. Otherwise, e.g. the universe of [B] in [Definition bar@{i} (A : Type@{i}) (B : Type)],
         the declaration is refused: the type would be less general than the one written. *)
      minimize_not_to_set u acc
  in
  if solve_flexibles then
    let fold_arbitrary u (flex, variances, graph as acc) =
      if not (Level.Set.mem u flex) then acc
      else simplify_arbitrary u acc
    in
    let (flex, _, _ as acc) = Level.Set.fold fold_arbitrary flex acc in
    (* The universes still undefined cannot stay either, and an algebraic lower bound is their
       only possible value: as a last resort, it is allowed even where their folded occurrences
       are not covariant (see [algebraic_bound_allowed]), e.g. a universe whose only lower
       bound is [max(u, v)] and which occurs in the type of an instance of an inductive invariant
       in it. Otherwise the declaration would be refused. *)
    if Level.Set.is_empty flex then acc else begin
      closed_last_resort := true;
      Fun.protect ~finally:(fun () -> closed_last_resort := false)
        (fun () -> Level.Set.fold fold_arbitrary flex acc)
    end
  else acc

module UPairs = OrderedType.UnorderedPair(Universe)
module UPairSet = Stdlib.Set.Make (UPairs)

type extra = {
  weak_constraints : UPairSet.t;
  above_prop : Level.Set.t;
  above_zero : Level.Set.t;
  parameter_only : Level.Set.t;
  internal : Level.Set.t;
}

let empty_extra = {
  weak_constraints = UPairSet.empty;
  above_prop = Level.Set.empty;
  above_zero = Level.Set.empty;
  parameter_only = Level.Set.empty;
  internal = Level.Set.empty;
}

let extra_union a b = {
  weak_constraints = UPairSet.union a.weak_constraints b.weak_constraints;
  above_prop = Level.Set.union a.above_prop b.above_prop;
  above_zero = Level.Set.union a.above_zero b.above_zero;
  parameter_only = Level.Set.union a.parameter_only b.parameter_only;
  internal = Level.Set.union a.internal b.internal;
}

let nf_extra nf a =
  let add (l, r) weak =
    let l = nf l and r = nf r in
    if Universe.equal l r then weak else UPairSet.add (l, r) weak
  in
  { a with weak_constraints = UPairSet.fold add a.weak_constraints UPairSet.empty }

let remove_from_extra removed a =
  let mentions_removed u = Universe.exists (fun (l, _) -> Level.Set.mem l removed) u in
  let filter (l, r) = not (mentions_removed l || mentions_removed r) in
  { weak_constraints = UPairSet.filter filter a.weak_constraints;
    above_zero = Level.Set.diff a.above_zero removed;
    above_prop = Level.Set.diff a.above_prop removed;
    parameter_only = Level.Set.diff a.parameter_only removed;
    internal = Level.Set.diff a.internal removed; }

(* let pr_universe_set prl s =
  let open Pp in
  str "{" ++ LevelExpr.Set.fold (fun lk acc -> LevelExpr.pr prl lk ++ str", " ++ acc) s (mt()) ++ str "}"  *)

let pr_universe_set prl s =
  let open Pp in
  str "{" ++ Universe.Set.fold (fun lk acc -> Universe.pr prl lk ++ str", " ++ acc) s (mt()) ++ str "}"

let _pr_partition prl m =
  let open Pp in
  prlist_with_sep spc (fun s -> pr_universe_set prl s ++ fnl ()) m

let _pr_substitution prl m =
  let open Pp in
  prlist_with_sep spc (fun (l, u) -> prl l ++ str" := " ++ Universe.pr prl u ++ fnl ()) (Level.Map.bindings m)

let new_minimize_weak ?entailed_only partial flex weak (g, variances) =
  UPairSet.fold (fun (u,v) (flex, variances, g as acc) ->
    let norm = Universe.subst_opt_fn (UGraph.normalize g) in
    let u = norm u and v = norm v in
    if (Universe.is_type0 u || Universe.is_type0 v) then acc
    else
      let check_le a b = UGraph.check_constraint g (a,Le,b) in
      let set a b variances =
        if not (algebraic_bound_allowed a b variances) then acc else
        (* With [Universe Minimization Compat], a universe occurring in the type of the declaration
           only with another flexible universe: it could be identified with a global universe,
           constraining nothing but losing its generality, e.g. when another weak constraint
           identified a universe of the body with it *)
        let to_flexible = match Universe.level b with
          | Some b -> Level.Set.mem b flex
          | None -> false
        in
        if not partial && get_compat_minimization () && occurs_in_type a variances && not to_flexible
        then acc else
        (* Before the minimization (see [early_minimize_weak]), only when this constrains no other
           universe, and a universe relevant to the type only with another flexible universe *)
        if (match entailed_only with
            | None -> false
            | Some free ->
              not ((free a || to_flexible) && UGraph.substitution_entailed_univ ~free [(a, b)] g))
        then acc else
        try
          let g, equivs = UGraph.set a b g in
          debug Pp.(fun () -> str"Minimize_weak: setting " ++ Level.raw_pr a ++ str" to " ++ Universe.pr Level.raw_pr b);
          update_equivs_bound (flex, variances, g) a b equivs
        with Loop_checking.NotCanonical -> assert false
           | UGraph.InconsistentEquality | UGraph.OccurCheck -> acc
      in
      (* With [Universe Minimization Compat], as the minimization ignoring variances did, the
         flexible side is also identified with the other one when it does not occur in the type of
         the declaration and the identification constrains no other universe: it is not bounded
         from above, and its lower bound is below the other side. E.g. the universes of the
         instances of the obligations of a [Program] definition, created by their proofs and only
         weakly related to the universes of the definition. *)
      let unbounded_irrelevant_to_type a b =
        not partial && get_compat_minimization () &&
        (let _, typev, _, _ = variance_info a flex variances in
         typev == UVars.Variance.Irrelevant) &&
        not (in_declared_type a variances) &&
        not (UGraph.has_upper_bound a g) &&
        match UGraph.lower_bound a g with
        | None -> true
        | Some lbound -> check_le lbound b
      in
      let set_to a b =
        let levels = Universe.levels b in
        let sup_variances = sup_variances variances (Level.Set.add a levels) in
        match InferCumulativity.term_type_variances sup_variances with
        | (None | Some UVars.Variance.Irrelevant), (None | Some UVars.Variance.Irrelevant),
          (None | Some Irrelevant) -> (* Irrelevant *)
          let variances =
            Level.Set.fold (fun bl variances -> set_variance variances bl sup_variances) levels variances
          in
          set a b variances
        | _, _, _ -> (* One universe is not irrelevant *)
          if unbounded_irrelevant_to_type a b then set a b variances
          else (flex, variances, g)
      in
      if check_le u v || check_le v u
      then acc
      else match Universe.level u with
      | Some u when Level.Set.mem u flex -> set_to u v
      | _ ->
        match Universe.level v with
        | Some v when Level.Set.mem v flex -> set_to v u
        | _ -> acc)
    weak (flex, variances, g)

(** The weak constraints applied before the minimization with [Universe Minimization Compat], only
  when they constrain no other universe: all the constraints on the substituted universes must
  still hold once substituted, possibly by raising or lowering the universes irrelevant to the type
  of the declaration, which can take any value ([UGraph.substitution_entailed_univ]). Unlike after
  the minimization, their bounds are not resolved yet: e.g. a universe [x <= u] of the body,
  identified with a global universe [g], would make [g <= u]. First jointly, those identifying a flexible universe
  irrelevant to the type of the declaration with the other side, as they often cannot be
  identified one at a time: e.g. the universes [a, b] of an occurrence [f@{a b}] of a constant with [a ~ max(u, v, w)],
  [b ~ max(u, v, w)], and those of its arguments, [x ~ v], [y ~ w] with [x <= a], [y <= a]. Then
  one at a time. *)
let early_minimize_weak flex weak (g, variances) =
  let norm = Universe.subst_opt_fn (UGraph.normalize g) in
  let irrelevant_to_type a =
    Level.Set.mem a flex &&
    let _, typev, typingv, _ = variance_info a flex variances in
    typev == UVars.Variance.Irrelevant && typingv == UVars.Variance.Irrelevant &&
    not (in_declared_type a variances) && not (occurs_in_type a variances)
  in
  let candidates = UPairSet.fold (fun (u, v) cands ->
      let u = norm u and v = norm v in
      let candidate a b =
        match Universe.level a with
        | Some a when irrelevant_to_type a && not (Level.Set.mem a (Universe.levels b))
                      && not (Level.Map.mem a cands) && algebraic_bound_allowed a b variances -> Some (a, b)
        | _ -> None
      in
      if Universe.is_type0 u || Universe.is_type0 v
         || UGraph.check_constraint g (u, Le, v) || UGraph.check_constraint g (v, Le, u)
      then cands
      else match candidate u v with
        | Some (a, b) -> Level.Map.add a b cands
        | None -> match candidate v u with Some (a, b) -> Level.Map.add a b cands | None -> cands)
      weak Level.Map.empty
  in
  (* The chains [x ~ y ~ z] are followed: the other sides are substituted too, and the candidates
     whose substitution is cyclic are dropped *)
  let rec resolve n b =
    let b' = Universe.subst_opt_fn (fun l -> Level.Map.find_opt l candidates) b in
    if Universe.equal b b' then Some b
    else if Int.equal n 0 then None
    else resolve (n - 1) b'
  in
  let bound = Level.Map.cardinal candidates in
  let candidates = Level.Map.fold (fun a b cands ->
      match resolve bound b with
      | Some b when not (Level.Set.mem a (Universe.levels b)) -> (a, b) :: cands
      | _ -> cands)
      candidates []
  in
  (* The greatest entailed subset: the candidates whose constraints do not hold are removed, and
     the others checked again without them *)
  let rec entailed_subset n candidates =
    if Int.equal n 0 || List.is_empty candidates then [] else
    match UGraph.substitution_failures_univ ~free:irrelevant_to_type candidates g with
    | None -> []
    | Some [] -> candidates
    | Some failures ->
      debug Pp.(fun () -> str"Minimize_weak: not entailed jointly: " ++ prlist_with_sep spc Level.raw_pr failures);
      let candidates = List.filter (fun (a, _) -> not (List.mem_f Level.equal a failures)) candidates in
      (* The other sides mentioning a removed candidate are no longer substituted *)
      let candidates = List.filter (fun (_, b) ->
          Level.Set.for_all (fun l -> not (List.mem_f Level.equal l failures)) (Universe.levels b))
          candidates
      in
      entailed_subset (n - 1) candidates
  in
  debug Pp.(fun () -> str"Minimize_weak: joint candidates: " ++ prlist_with_sep spc (fun (a, b) -> Level.raw_pr a ++ str" := " ++ Universe.pr Level.raw_pr b) candidates);
  let candidates = entailed_subset (List.length candidates) candidates in
  let acc = (flex, variances, g) in
  let acc =
    if List.is_empty candidates then acc
    else List.fold_left (fun (flex, variances, g as acc) (a, b) ->
        match UGraph.set a b g with
        | g, equivs ->
          debug Pp.(fun () -> str"Minimize_weak: setting jointly " ++ Level.raw_pr a ++ str" to " ++ Universe.pr Level.raw_pr b);
          update_equivs_bound (flex, variances, g) a b equivs
        | exception (Loop_checking.NotCanonical | UGraph.InconsistentEquality | UGraph.OccurCheck) -> acc)
        acc candidates
  in
  let flex, variances, g = acc in
  new_minimize_weak ~entailed_only:irrelevant_to_type false flex weak (g, variances)

(** The universes of [parameter_only] are set to their lower bound, [Set] included whatever
  [Universe Minimization ToSet]: they only bound the types of the arguments of one occurrence of
  a global, so they cannot make anything less general (an upper bound, e.g. from the sort of the
  type they occur in, still holds of the lower bound). Not with partial information, where the
  rest of the definition may still bound them, nor when the substitution would also set a
  universe which is not one of them. *)
let minimize_parameter_only solve_flexibles partial above_zero parameter_only (flex, variances, graph as acc) =
  if partial then acc else
  let require_entailed = not solve_flexibles in
  let minimize u (flex, variances, graph as acc) =
    if not (Level.Set.mem u flex) then acc
    else match UGraph.minimize ~require_entailed u graph with
      | HasSubst (graph', equivs, lbound) ->
        (* The universe may have escaped its positions, e.g. into the type of a binder [B : ?T]
           whose type [?T] was solved to [Type@{u}] by [@sig@{u v} B P]: it must also be
           irrelevant to the type and typing of the definition *)
        (* With [Universe Minimization Compat], it must not occur in the type of the declaration
           either, even irrelevantly: the unification of this type would make [Set] reach
           positions where it matters, as for the universes not occurring in the type (see
           [simplify_variables]). Unless it is above a type in [Set] ([above_zero], e.g. the
           universe of [Fin n] in [sig@{u v} (Fin n) P]), where [Set] is its natural value. *)
        let parameter_only_level l =
          (Level.equal l u || Level.Set.mem l parameter_only) &&
          let _, typev, typingv, _ = variance_info l flex variances in
          typev == UVars.Variance.Irrelevant && typingv == UVars.Variance.Irrelevant &&
          not (get_compat_minimization () && occurs_in_type l variances &&
               not (Level.Set.mem l above_zero))
        in
        if parameter_only_level u && List.for_all (fun (l, _) -> parameter_only_level l) equivs
           && algebraic_bound_allowed u lbound variances then begin
          debug_each Pp.(fun () -> str"Minimizing parameter-only " ++ Level.raw_pr u ++ str" to " ++ Universe.pr Level.raw_pr lbound);
          update_equivs_bound (flex, variances, graph') u lbound equivs
        end
        else acc
      | NoBound | CannotSimplify -> acc
  in
  Level.Set.fold minimize parameter_only acc

let normalize_context_set ~solve_flexibles ~solve_term ?(minimize_internal=false) ~variances ~partial graph
  ~flexible_variables ?binders
  {weak_constraints=weak;above_prop; above_zero; parameter_only; internal} =
  let prl = UnivNames.pr_level_with_global_universes ?binders in
  debug Pp.(fun () -> str "Minimizing context: " ++ UGraph.pr_universes prl (UGraph.repr ~local:true graph) ++ spc () ++
    str"Flexible variables: " ++ Level.Set.pr Level.raw_pr flexible_variables ++ fnl () ++
    str"Variances: " ++ pr_variances prl variances ++ fnl () ++
    str"Above prop: " ++ Level.Set.pr Level.raw_pr above_prop ++ fnl () ++
    str"Above zero: " ++ Level.Set.pr Level.raw_pr above_zero ++ fnl () ++
    str"Parameter-only: " ++ Level.Set.pr Level.raw_pr parameter_only ++ fnl () ++
    str"Weak constraints " ++
    prlist_with_sep spc (fun (u,v) -> Universe.pr Level.raw_pr u ++ str" ~ " ++ Universe.pr Level.raw_pr v)
     (UPairSet.elements weak) ++ spc () ++
     (if partial then str"In partial mode" else str"In non-partial mode") ++ spc () ++
    if solve_flexibles then str "solving all flexibles" else str" solving flexibles respecting variances information");
  debug_graph Pp.(fun () ->
     str"Graph: " ++ UGraph.pr_model graph);
  if CDebug.get_flag _debug_minim then
    if not (Level.Set.is_empty flexible_variables) && InferCumulativity.is_empty_variances variances then
      Feedback.msg_debug Pp.(str"normalize_context_set called with empty variance information");
  (* Now we construct the instantiation of each variable. *)
  let flexible_variables, variances, graph =
    (* debug Pp.(fun () -> str"Model after removal: " ++ UGraph.pr_model graph); *)
    (* With [Universe Minimization Compat], the weak constraints are applied first, as the
       minimization ignoring variances did: otherwise the universes of the body only weakly related
       to the universes of the type, e.g. by a conversion of their types up to reduction, would be
       set to [Set] as universes not occurring in the type, and the weak constraints with them
       would be lost. Before the minimization, identifying a universe with an algebraic one, e.g.
       [max(u, v)], could bound its lower bounds by it: these are only applied when this
       constrains no other universe (see [early_minimize_weak]) *)
    let flexible_variables, variances, graph =
      if partial || not (get_compat_minimization ()) then flexible_variables, variances, graph
      else early_minimize_weak flexible_variables weak (graph, variances)
    in
    let flexible_variables, variances, graph =
      minimize_parameter_only solve_flexibles partial above_zero parameter_only (flexible_variables, variances, graph) in
    let internal = if minimize_internal then internal else Level.Set.empty in
    let flex, variances, graph = simplify_variables solve_flexibles above_prop above_zero internal partial solve_term flexible_variables variances graph in
    debug_graph Pp.(fun () -> str"Model after simplification: " ++ UGraph.pr_model graph ++ fnl () ++ Level.Set.pr Level.raw_pr flex);
    new_minimize_weak partial flex weak (graph, variances)
  in
  debug Pp.(fun () ->
    str "After minimization: " ++ fnl () ++
    str"Flexible variables: " ++ Level.Set.pr Level.raw_pr flexible_variables ++ fnl () ++
    str"Variances: " ++ pr_variances prl variances ++ fnl () ++
    UGraph.pr_universes prl (UGraph.repr ~local:true graph));
  flexible_variables, variances, graph
