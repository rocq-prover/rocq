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
open UVars

let _debug_ugraph, debug = CDebug.create_full ~name:"uGraph" ()

module G = Loop_checking
(* Do not include G to make it easier to control universe specific
   code (eg add_universe with a constraint vs G.add with no
   constraint) *)

type t = {
  graph: G.t;
  type_in_type : bool;
  (* above_prop only for checking template poly! *)
  above_prop_qvars : Sorts.QVar.Set.t;
}

type locality = Loop_checking.locality = Global | Local

(* Universe inconsistency: error raised when trying to enforce a relation
   that would create a cycle in the graph of universes. *)

type path_explanation = G.explanation Lazy.t

type explanation =
  | Path of path_explanation
  | Other of Pp.t

type univ_variable_printers = (Sorts.QVar.t -> Pp.t) * (Level.t -> Pp.t)
type univ_inconsistency = univ_variable_printers option * (constraint_type * Sorts.t * Sorts.t * explanation option)

exception UniverseInconsistency of univ_inconsistency

type 'a check_function = t -> 'a -> 'a -> bool

let set_type_in_type b g = {g with type_in_type=b}

let type_in_type g = g.type_in_type

let graph_check_leq g u v = G.check_leq g.graph u v
let graph_check_eq g u v = G.check_eq g.graph u v

let check_leq g u v =
  type_in_type g || Universe.equal u v || graph_check_leq g u v

let check_leq g u u' =
  let res = check_leq g u u' in
  debug Pp.(fun () -> str"check_leq: " ++ Universe.pr Level.raw_pr u ++
    str" <= " ++ Universe.pr Level.raw_pr u' ++ str" = " ++ bool res);
  res

let check_eq g u v =
  type_in_type g || Universe.equal u v || graph_check_eq g u v

let empty_universes = {graph=G.empty; type_in_type=false; above_prop_qvars=Sorts.QVar.Set.empty}

let initial_universes =
  let g = G.empty in
  let g = G.add ~rigid:true Level.set g in
  {empty_universes with graph=g }

let set_local g =
  { g with graph = G.set_local g.graph }

type level_equivalences = (Level.t * (Level.t * int)) list

let enforce_constraint (u,d,v) g =
  match d with
  | Le -> G.enforce_leq u v g.graph
  | Eq -> G.enforce_eq u v g.graph

let enforce_constraint0 cst g = match enforce_constraint cst g with
| None -> None
| Some (g', equivs) ->
  if g' == g.graph then Some (g, equivs)
  else Some ({ g with graph = g' }, equivs)

let enforce_constraint cst g = match enforce_constraint0 cst g with
| None ->
  if not (type_in_type g) then
    let (u, c, v) = cst in
    let e = lazy (G.get_explanation cst g.graph) in
    let mk u = Sorts.sort_of_univ u in
    raise (UniverseInconsistency (None, (c, mk u, mk v, Some (Path e))))
  else g, []
| Some g -> g

let merge_constraints csts g =
  Constraints.fold (fun cst (g, equivs) ->
    let g, equivs' = enforce_constraint cst g in
    g, equivs' @ equivs) csts (g, [])

let check_constraint { graph = g; type_in_type; _ } (u,d,v) =
  type_in_type
  || match d with
  | Le -> G.check_leq g u v
  | Eq -> G.check_eq g u v

let check_constraints csts g = Constraints.for_all (check_constraint g) csts

let normalize { graph = g; _ } l = G.normalize g l

exception InconsistentEquality = G.InconsistentEquality
exception OccurCheck = G.OccurCheck

let set l u g =
  let g', equivs = G.set l u g.graph in
  { g with graph = g' }, equivs

exception AlreadyDeclared = G.AlreadyDeclared
let add_universe u ~strict ~rigid g =
  let graph = G.add ~rigid u g.graph in
  let b = if strict then Universe.type1 else Universe.type0 in
  fst (enforce_constraint (b, Le, Universe.make u) { g with graph })

let switch_locality u g = { g with graph = G.switch_locality u g.graph }

let check_declared_universes g l =
  G.check_declared g.graph l

let is_declared g l =
  G.is_declared g.graph l

let minimize l g =
  match G.minimize l g.graph with
  | G.HasSubst (graph, equivs, lbound) -> G.HasSubst ({ g with graph }, equivs, lbound)
  | G.NoBound -> G.NoBound
  | G.CannotSimplify -> G.CannotSimplify

let maximize l g =
  match G.maximize l g.graph with
  | G.HasSubst (graph, equivs, lbound) -> G.HasSubst ({ g with graph }, equivs, lbound)
  | G.NoBound -> G.NoBound
  | G.CannotSimplify -> G.CannotSimplify

let remove_set_clauses l g =
  let graph = G.remove_set_clauses l g.graph in
  { g with graph }

let pr_model ?local g = G.pr_model ?local g.graph

let constraints_of_universes ?(only_local=false) g =
  let add cst accu = Constraints.add cst accu in
  G.constraints_of g.graph ~only_local add Constraints.empty
let constraints_for ~kept g =
  let add cst accu = Constraints.add cst accu in
  G.constraints_for ~kept g.graph add Constraints.empty

let remove removed g =
  { g with graph = G.remove removed g.graph }

let subst ?(local=false) g = G.subst ~local g.graph

(** Subtyping of polymorphic contexts *)

let check_subtype univs ctxT ctx =
  (* NB: size check is the only constraint on qualities *)
  if eq_sizes (AbstractContext.size ctxT) (AbstractContext.size ctx) then
    let uctx = AbstractContext.repr ctx in
    let inst = UContext.instance uctx in
    let cst = UContext.constraints uctx in
    let cstT = UContext.constraints (AbstractContext.repr ctxT) in
    let push accu v = add_universe v ~strict:false ~rigid:true accu in
    let univs = Array.fold_left push univs (snd (LevelInstance.to_array inst)) in
    let univs, _equivs = merge_constraints cstT univs in
    check_constraints cst univs
  else false

(** Instances *)

let check_eq_instances g t1 t2 =
  let qt1, ut1 = Instance.to_array t1 in
  let qt2, ut2 = Instance.to_array t2 in
  CArray.equal Sorts.Quality.equal qt1 qt2
  && CArray.equal (check_eq g) ut1 ut2

let domain g = G.domain g.graph

let variables ~local ~with_subst g = G.variables ~local ~with_subst g.graph

let check_universes_invariants g = G.check_invariants ~required_canonical:Level.is_set g.graph

(** Sort comparison *)

(* The functions below rely on the invariant that no universe in the graph
   can be unified with Prop / SProp. This is ensured by UGraph, which only
   contains Set as a "small" level. *)

open Sorts

let get_algebraic = function
| Prop | SProp -> assert false
| Set -> Universe.type0
| Type u | QSort (_, u) -> u

let check_eq_sort ugraph s1 s2 = match s1, s2 with
| (SProp, SProp) | (Prop, Prop) | (Set, Set) -> true
| (SProp, _) | (_, SProp) | (Prop, _) | (_, Prop) ->
  type_in_type ugraph
| (Type _ | Set), (Type _ | Set) ->
  check_eq ugraph (get_algebraic s1) (get_algebraic s2)
| QSort (q1, u1), QSort (q2, u2) ->
  QVar.equal q1 q2 && check_eq ugraph u1 u2
| (QSort _, (Type _ | Set)) | ((Type _ | Set), QSort _) -> false

let is_above_prop ugraph q =
  Sorts.QVar.Set.mem q ugraph.above_prop_qvars

let check_leq_sort ugraph s1 s2 = match s1, s2 with
| (SProp, SProp) | (Prop, Prop) | (Set, Set) -> true
| (SProp, _) -> type_in_type ugraph
| (Prop, SProp) -> type_in_type ugraph
| (Prop, (Set | Type _)) -> true
| (Prop, QSort (q,_)) -> is_above_prop ugraph q
| (_, (SProp | Prop)) -> type_in_type ugraph
| (Type _ | Set), (Type _ | Set) ->
  check_leq ugraph (get_algebraic s1) (get_algebraic s2)
| QSort (q1, u1), QSort (q2, u2) ->
  QVar.equal q1 q2 && check_leq ugraph u1 u2
| QSort (q, _), Set -> is_above_prop ugraph q
| QSort (q, u1), Type u2 -> is_above_prop ugraph q && check_leq ugraph u1 u2
| ((Type _ | Set), QSort _) -> false

(** Pretty-printing *)

let pr_pmap sep pr map =
  let cmp (u,_) (v,_) = Level.compare u v in
  Pp.prlist_with_sep sep pr (List.sort cmp (Level.Map.bindings map))

let pr_arc prl = let open Pp in
  function
  | u, G.Node l ->
    if CList.is_empty l then mt ()
    else
      (* In increasing order *)
      let l = List.sort (fun (i, _) (i', _) -> Int.compare i i') l in
      let l = CList.factorize_left Int.equal l in
      let pr_cstrs (i, l) =
        let l = List.sort Universe.compare l in
        let k, is_lt = if i >= 1 then pred i, true else 0, false in
        let u = (u, k) in
        LevelExpr.pr prl u ++ str " " ++ v 0
        (prlist_with_sep spc (fun v -> str (if is_lt then "< " else "<= ") ++ Universe.pr prl v) l)
      in
      prlist_with_sep fnl pr_cstrs l ++ fnl ()
  | u, G.Alias u' ->
    prl u  ++ str " = " ++ Universe.pr prl u' ++ fnl  ()

type node = G.node =
| Alias of Universe.t
| Node of (int * Universe.t) list (** Nodes [(k_i, u_i); ...] s.t. u + k_i <= u_i *)

let repr ?(local=false) g = G.repr ~local g.graph

let pr_universes prl g = pr_pmap Pp.mt (pr_arc prl) g

let pr ?(local=false) prl g = pr_universes prl (repr ~local g)

open Pp

let explain_universe_inconsistency default_prq default_prl (printers, (o,u,v,p) : univ_inconsistency) =
  let prq, prl = match printers with
    | Some (prq, prl) -> prq, prl
    | None -> default_prq, default_prl
  in
  let pr_uni u = match u with
  | Sorts.Set -> str "Set"
  | Sorts.Prop -> str "Prop"
  | Sorts.SProp -> str "SProp"
  | Sorts.Type u -> Universe.pr prl u
  | Sorts.QSort (q, u) -> str "Type@{" ++ prq q ++ str " ; " ++ Universe.pr prl u ++ str"}"
  in
  let pr_rel = function
    | Eq -> str"=" | Le -> str"≤"
  in
  let pr_erel = function
    | G.UEq -> str"=" | G.ULe -> str"≤" | G.ULt -> str"<"
  in
  let reason = match p with
    | None -> mt()
    | Some (Other p) -> spc() ++ p
    | Some (Path p) ->
      let pstart, p = Lazy.force p in
      if p = [] then mt ()
      else
        str " because" ++ spc() ++ Universe.pr prl pstart ++
        prlist (fun (r,v) -> spc() ++ pr_erel r ++ str" " ++ Universe.pr prl v) p
  in
    str "Cannot enforce" ++ spc() ++ pr_uni u ++ spc() ++
      pr_rel o ++ spc() ++ pr_uni v ++ reason

module Internal = struct

  let add_template_qvars qvars g =
    assert (Sorts.QVar.Set.is_empty g.above_prop_qvars);
    {g with above_prop_qvars=qvars}

  let is_above_prop = is_above_prop
end
