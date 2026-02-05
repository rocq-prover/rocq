(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
open Sorts

module ElimTable = struct
  open Quality

  let const_eliminates_to q q' =
    match q, q' with
    | QType, _ -> true
    | QProp, (QProp | QSProp) -> true
    | QSProp, QSProp -> true
    | (QProp | QSProp), _ -> false

  let eliminates_to q q' =
    match q, q' with
    | QConstant QType, _ -> true
    | QConstant q, QConstant q' -> const_eliminates_to q q'
    | QVar q, QVar q' -> QVar.equal q q'
    | (QConstant _ | QVar _), _ -> false
end

module G = AcyclicGraph.Make(struct
    type t = Quality.t
    module Set = Quality.Set
    module Map = Quality.Map

    let equal = Quality.equal
    let compare = Quality.compare

    let raw_pr = Quality.raw_pr

    let anomaly_err q = Pp.(str "Quality " ++ Quality.raw_pr q ++ str " undefined.")
  end)
(** We only use G to track connected components of the eliminability relation.
    In particular, G |= q1 = q2 does not mean that they are equal, but just
    equi-eliminable. As a result, one should not use the check_eq / enforce_eq
    functions in the remainder of this module.

    Note that we also abuse the Lt relation to get some rigidity for free for
    the built-in sorts, but this is a hack that should go away at some point. *)

module RigidPaths = struct
  type t = (Quality.t list) Quality.Map.t

  let add_elim_to q1 q2 g =
    let upd ls =
      Some (match ls with
        | Some ls -> q2 :: ls
        | None -> [q2])
    in
    Quality.Map.update q1 upd g

  let empty : t = Quality.Map.empty

  let dfs q g =
    let rec aux seen q =
      if Quality.Set.mem q seen
      then seen
      else
        let seen = Quality.Set.add q seen in
        match Quality.Map.find_opt q g with
        | None -> seen
        | Some ls -> List.fold_left aux seen ls
  in aux Quality.Set.empty q

  let check_forbidden_path (map : Quality.Set.t Quality.Map.t) g =
    let fold q s ls =
      let allowed = dfs q g in
      let diff = Quality.Set.diff s allowed in
      if Quality.Set.is_empty diff
      then ls
      else List.append (List.map (fun q' -> (q, q')) (List.of_seq @@ Quality.Set.to_seq diff)) ls in
    let forbidden = Quality.Map.fold fold map [] in
    match forbidden with
    | [] -> None
    | p :: _ -> Some p
end

module QMap = QVar.Map
module QSet = QVar.Set

type t =
  { graph: G.t;
    (** Connected components of the eliminability graph *)
    rigid_paths: RigidPaths.t;
    ground_and_global_sorts: Quality.Set.t;
    dominant: Quality.t QMap.t;
    delayed_check: QSet.t QMap.t;
    ignore_constraints: bool;
  }

type path_explanation = G.explanation Lazy.t

type explanation =
  | Path of path_explanation
  | Other of Pp.t

type quality_inconsistency =
  ((QVar.t -> Pp.t) option) *
    (ElimConstraint.kind * Quality.t * Quality.t * explanation option)

(* If s can eliminate to s', we want an edge between s and s'.
   In the acyclic graph, it means setting s to be lower or equal than s'.
   This function ensures a uniform behaviour between [check] and [enforce]. *)
let to_graph_cstr k =
  let open ElimConstraint in
  match k with
  | ElimTo -> AcyclicGraph.Le

type elimination_error =
  | IllegalConstraintFromSProp of Quality.t
  | IllegalConstantConstraint of Quality.constant * Quality.constant
  | CreatesForbiddenPath of Quality.t * Quality.t
  | MultipleDominance of Quality.t * Quality.t * Quality.t
  | QualityInconsistency of quality_inconsistency

exception EliminationError of elimination_error

let set_ignore_constraints b g = {g with ignore_constraints=b}
let ignore_constraints g = g.ignore_constraints

let non_refl_pairs l =
  let fold x =
    List.fold_right (fun y acc -> if x <> y then (x,y) :: acc else acc) l in
  List.fold_right fold l []

let get_new_rigid_paths g p dom =
  let add (q1,_,q2) accu =
    Quality.Map.update q1
      (fun ls -> Some (match ls with Some ls -> Quality.Set.add q2 ls | None -> Quality.Set.singleton q2))
      accu in
  let all_paths = G.constraints_for ~kept:dom g add Quality.Map.empty in
  RigidPaths.check_forbidden_path all_paths p

let set_dominant g qv q =
  { g with dominant = QMap.add qv q g.dominant }

(* Set the dominant sort of qv to the minimum between q1 and q2 if they are related.
   [q1] is the dominant of qv in [g]. *)
let update_dominant_if_related g qv q1 q2 =
  if G.check_leq g.graph q1 q2 then Some (set_dominant g qv q2)
  else if G.check_leq g.graph q2 q1 then Some g
  else None

(* If [qv] is not dominated, set dominance to [q].
   Otherwise, checks whether the dominant of [qv] and [q] are related.
   If so, puts the smallest of the two as the dominant of [qv]. *)
let rec update_dominance g q qv =
  let g' = match QMap.find_opt qv g.dominant with
    | None -> Some (set_dominant g qv q)
    | Some q' -> update_dominant_if_related g qv q' q in
  match QMap.find_opt qv g.delayed_check with
  | None -> g'
  | Some qs ->
     let g' = QSet.fold (fun v g -> Option.bind g (fun g -> update_dominance g q v)) qs g' in
     match g' with
     | Some graph -> Some { graph with delayed_check = QMap.set qv QSet.empty g.delayed_check }
     | None -> None

let update_dominance_if_valid g (q1,k,q2) =
  match k with
  | ElimConstraint.ElimTo ->
     (* if the constraint is s ~> g, dominants are not modified. *)
     if Quality.is_qconst q2 then Some g
     else
       match q1, q2 with
       | (Quality.QConstant _ | Quality.QVar _), Quality.QConstant _ -> assert false
       | Quality.QVar qv1, Quality.QVar qv2 ->
          (* 3 cases:
             - if [qv1] is a global, treat as constants.
             - if [qv1] is not dominated, delay the check to when [qv1] gets dominated.
             - if [qv1] is dominated, try to update the dominance of [qv2]. *)
          if Quality.is_qglobal q1 then update_dominance g q1 qv2
          else
            (match QMap.find_opt qv1 g.dominant with
            | None ->
               let add_delayed qs =
                 Some { g with delayed_check = QMap.set qv1 (QSet.add qv2 qs) g.delayed_check }
               in
               (match QMap.find_opt qv1 g.delayed_check with
               | None -> add_delayed QSet.empty
               | Some qs -> add_delayed qs)
            | Some q' -> update_dominance g q' qv2)
       | Quality.QConstant _, Quality.QVar qv -> update_dominance g q1 qv

let dominance_check g (q1,_,q2 as cstr) =
  let dom_q1 () = match q1 with
    | Quality.QConstant _ -> q1
    | Quality.QVar qv ->
       if Quality.is_qglobal q1 then q1
       else QMap.find qv g.dominant in
  let dom_q2 () = match q2 with
    | Quality.QConstant _ -> assert false
    | Quality.QVar qv -> QMap.find qv g.dominant in
  match update_dominance_if_valid g cstr with
  | None -> raise (EliminationError (MultipleDominance (dom_q2() , q2, dom_q1())))
  | Some g -> g

let check_rigid_paths g =
  let paths = get_new_rigid_paths g.graph g.rigid_paths g.ground_and_global_sorts in
  match paths with
  | None -> ()
  | Some (q1, q2) -> raise (EliminationError (CreatesForbiddenPath (q1, q2)))

let add_rigid_path q1 q2 g =
  let open Quality in
  match q1, q2 with
  (* Adding a constraint from SProp -> * is not allowed *)
  | QConstant QSProp, _ -> raise (EliminationError (IllegalConstraintFromSProp q2))
  (* Adding constraints between constants is not allowed *)
  | QConstant qc1, QConstant qc2 -> raise (EliminationError (IllegalConstantConstraint (qc1, qc2)))
  | _, _ -> { g with rigid_paths = RigidPaths.add_elim_to q1 q2 g.rigid_paths }

let enforce_func k q1 q2 g = match k with
| ElimConstraint.ElimTo ->
  begin match G.enforce_leq q1 q2 g.graph with
  | None -> None
  | Some graph -> Some { g with graph }
  end

let enforce_constraint (q1, k, q2) g =
  match enforce_func k q1 q2 g with
  | None ->
     if ignore_constraints g then g else
     let e = lazy (G.get_explanation (q1,to_graph_cstr k,q2) g.graph) in
     raise @@ EliminationError (QualityInconsistency (None, (k, q1, q2, Some (Path e))))
  | Some g ->
    dominance_check g (q1, k, q2)

let merge_constraints csts g = ElimConstraints.fold enforce_constraint csts g

let check_constraint g (q1, k, q2) =
  ignore_constraints g ||
  match k with
  | ElimConstraint.ElimTo -> G.check_leq g.graph q1 q2

let check_constraints csts g = ElimConstraints.for_all (check_constraint g) csts

exception AlreadyDeclared = G.AlreadyDeclared

let add_quality q g =
  let graph = G.add q g.graph in
  let g = enforce_constraint (Quality.qtype, ElimConstraint.ElimTo, q) { g with graph } in
  let (paths,ground_and_global_sorts) =
    if Quality.is_qglobal q
    then (RigidPaths.add_elim_to Quality.qtype q g.rigid_paths, Quality.Set.add q g.ground_and_global_sorts)
    else (g.rigid_paths,g.ground_and_global_sorts) in
  (* As Type ~> s, set Type to be the dominant sort of q if q is a variable. *)
  let dominant = match q with
    | Quality.QVar qv -> QMap.add qv Quality.qtype g.dominant
    | Quality.QConstant _ -> g.dominant in
  { g with rigid_paths = paths; ground_and_global_sorts; dominant }

let enforce_eliminates_to s1 s2 g =
  enforce_constraint (s1, ElimConstraint.ElimTo, s2) g

let initial_graph =
  let g = G.empty in
  let g = List.fold_left (fun g q -> G.add q g) g Quality.all_constants in
  (* Enforces the constant constraints defined in the table of
     [Constants.eliminates_to] without reflexivity (should be consistent,
     otherwise the [Option.get] will fail). *)
  let fold (g,p) (q,q') =
    if ElimTable.eliminates_to q q'
    then (Option.get @@ G.enforce_lt q q' g, RigidPaths.add_elim_to q q' p)
    else (g,p)
  in
  let (g,p) = List.fold_left fold (g,RigidPaths.empty) @@ non_refl_pairs Quality.all_constants in
  { graph = g;
    rigid_paths = p;
    ground_and_global_sorts = Quality.Set.of_list Quality.all_constants;
    dominant = QMap.empty;
    delayed_check = QMap.empty;
    ignore_constraints = false }

let eliminates_to g q q' =
  ignore_constraints g ||
  G.check_leq g.graph q q'

let update_rigids g g' =
  { g' with rigid_paths = g.rigid_paths }

let sort_eliminates_to g s1 s2 =
  eliminates_to g (quality s1) (quality s2)

let eliminates_to_prop g q = eliminates_to g q Quality.qprop

let domain g = G.domain g.graph

let qvar_domain g =
  Quality.Set.fold
    (fun q acc -> match q with Quality.QVar q -> QVar.Set.add q acc | _ -> acc)
    (domain g) QVar.Set.empty

(* XXX the function below does not handle equivalence classes, but it's only used for printing *)
let merge g g' =
  let qs = domain g' in
  let g = Quality.Set.fold
             (fun q acc -> try add_quality q acc with _ -> acc) qs g in
  Quality.Set.fold
    (fun q -> Quality.Set.fold
             (fun q' acc -> if eliminates_to g' q q'
                         then enforce_eliminates_to q q' acc
                         else acc) qs) qs g

let is_empty g = QVar.Set.is_empty (qvar_domain g)

(* Pretty printing *)

let pr_pmap sep pr map =
  let cmp (q1, _) (q2, _) = Quality.compare q1 q2 in
  Pp.prlist_with_sep sep pr (List.sort cmp (Quality.Map.bindings map))

let pr_arc prq =
  let open Pp in
  function
  | q1, G.Node ltle ->
    if Quality.Map.is_empty ltle then mt ()
    else
      prq q1 ++ spc () ++
      v 0
        (pr_pmap spc (fun (q2, _) ->
              str "-> " ++ prq q2)
            ltle) ++
      fnl ()
  | q1, G.Alias q2 ->
    prq q1  ++ str " <-> " ++ prq q2 ++ fnl ()

let repr g = G.repr g.graph

let is_declared q g = match G.check_declared g.graph (Quality.Set.singleton q) with
| Result.Ok _ -> true
| Result.Error _ -> false

let pr_qualities prq g = pr_pmap Pp.mt (pr_arc prq) (repr g)

let explain_quality_inconsistency prv r =
  let open Pp in
  let pr_cst = function
    | AcyclicGraph.Eq -> str"="
    | AcyclicGraph.Le -> str"->"
    | AcyclicGraph.Lt -> str"->" (* Yes, it's the same as above. *)
  in
  match r with
  | None -> mt()
  | Some (Other p) -> p
  | Some (Path p) ->
     let pstart, p = Lazy.force p in
     if p = [] then mt ()
     else
       let qualities = pstart :: List.map snd p in
       let constants = List.filter Quality.is_qconst qualities in
       str "because it would identify " ++
         pr_enum (Quality.pr prv) constants ++
         spc() ++ str"which is inconsistent." ++ spc() ++
         str"This is introduced by the constraints " ++
         prlist (fun (r, v) -> Quality.pr prv v ++ spc() ++ pr_cst r ++ spc()) p ++
         Quality.pr prv pstart

let explain_elimination_error defprv err =
  let open Pp in
  match err with
  | IllegalConstraintFromSProp q -> str "Enforcing elimination constraints from SProp to any other sort is not allowed. " ++ brk (1, 0) ++
    str "This expression would enforce that SProp eliminates to " ++ Quality.pr defprv q ++ str "."
  | IllegalConstantConstraint (q1, q2) -> str "Enforcing elimination constraints between constant sorts (Type, Prop or SProp) is not allowed." ++ brk (1, 0) ++
    str "Here: " ++ Quality.Constants.pr q1 ++ str" and " ++ Quality.Constants.pr q2 ++ str "."
  | CreatesForbiddenPath (q1,q2) ->
     str "This expression would enforce a non-declared elimination constraint between" ++
       spc() ++ Quality.pr defprv q1 ++ spc() ++ str"and" ++ spc() ++ Quality.pr defprv q2
  | MultipleDominance (q1,qv,q2) ->
     let pr_elim q = Quality.pr defprv q ++ spc() ++ str"->" ++ spc() ++ Quality.pr defprv qv in
     str "This expression enforces" ++ spc() ++ pr_elim q1 ++ spc() ++ str"and" ++ spc() ++
       pr_elim q2 ++ spc() ++ str"which might make type-checking undecidable"
  | QualityInconsistency (prv, (k, q1, q2, r)) ->
     let prv = match prv with Some prv -> prv | None -> defprv in
     str"The quality constraints are inconsistent: " ++
       str "cannot enforce" ++ spc() ++ Quality.pr prv q1 ++ spc() ++
       ElimConstraint.pr_kind k ++ spc() ++ Quality.pr prv q2 ++ spc() ++
       explain_quality_inconsistency prv r
