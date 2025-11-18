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

module RigidPath = struct
  type t = Quality.t * Quality.t

  let compare (q1,q2) (q1',q2') =
    let i = Quality.compare q1 q1' in
    if i = 0 then Quality.compare q2 q2'
    else i
end

module RigidPaths = Set.Make(RigidPath)

module QMap = QVar.Map
module QSet = QVar.Set

type t =
  { graph: G.t;
    rigid_paths: RigidPaths.t;
    ground_and_global_sorts: Quality.t list;
    dominant: Quality.t QMap.t;
    delayed_check: QSet.t QMap.t;
  }

type path_explanation = G.explanation Lazy.t

type explanation =
  | Path of path_explanation
  | Other of Pp.t

type quality_inconsistency = (ElimConstraint.kind * Quality.t * Quality.t * explanation option)

(* If s can eliminate to s', we want an edge between s and s'.
   In the acyclic graph, it means setting s to be lower or equal than s'.
   This function ensures a uniform behaviour between [check] and [enforce]. *)
let to_graph_cstr k =
  let open ElimConstraint in
  match k with
    | ElimTo -> AcyclicGraph.Le
    | Equal -> AcyclicGraph.Eq

let check_func k =
  match k with
  | ElimConstraint.ElimTo -> G.check_leq
  | ElimConstraint.Equal -> G.check_eq

let enforce_func k =
  match k with
  | ElimConstraint.ElimTo -> G.enforce_leq
  | ElimConstraint.Equal -> G.enforce_eq

type constraint_source =
  | Internal
  | Rigid
  | Static

type elimination_error =
  | IllegalConstraint
  | CreatesForbiddenPath of Quality.t * Quality.t
  | MultipleDominance of Quality.t * Quality.t * Quality.t
  | QualityInconsistency of quality_inconsistency

exception EliminationError of elimination_error

let non_refl_pairs l =
  let fold x =
    List.fold_right (fun y acc -> if x <> y then (x,y) :: acc else acc) l in
  List.fold_right fold l []

let get_new_rigid_path g p dom =
  let n = List.length dom in
  if RigidPaths.cardinal p = n*(n+1)/2 then None
  else
    let forbidden = List.filter (fun u -> not (RigidPaths.mem u p)) @@ non_refl_pairs dom in
    let witness = List.filter (fun (q,q') -> check_func ElimConstraint.ElimTo g q q') forbidden in
    match witness with
    | [] -> None
    | x :: _ -> Some x

let add_transitive_rigid_paths q1 q2 p =
  let transitive_set = RigidPaths.filter (fun (q,_) -> Quality.equal q2 q) p in
  RigidPaths.fold (fun (_,q) p -> RigidPaths.add (q1,q) p) transitive_set p

let set_dominant g qv q =
  { g with dominant = QMap.add qv q g.dominant }

(* Set the dominant sort of qv to the minimum between q1 and q2 if they are related.
   [q1] is the dominant of qv in [g]. *)
let update_dominant_if_related g qv q1 q2 =
  if check_func ElimConstraint.ElimTo g.graph q1 q2 then Some (set_dominant g qv q2)
  else if check_func ElimConstraint.ElimTo g.graph q2 q1 then Some g
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
  | ElimConstraint.Equal -> Some g
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

let enforce_constraint src (q1,k,q2) g =
  match enforce_func k q1 q2 g.graph with
  | None ->
     let e = lazy (G.get_explanation (q1,to_graph_cstr k,q2) g.graph) in
     raise @@ EliminationError (QualityInconsistency (k, q1, q2, Some (Path e)))
  | Some graph ->
     let g = match src with
       | Static -> { g with graph }
       | Rigid ->
          if (Quality.is_qconst q1 && Quality.is_qconst q2) ||
               (Quality.is_qsprop q1 && not (Quality.is_qsprop q2))
          then raise (EliminationError IllegalConstraint)
          else { g with graph; rigid_paths = RigidPaths.add (q1,q2) @@ add_transitive_rigid_paths q1 q2 g.rigid_paths }
       | Internal ->
          match get_new_rigid_path g.graph g.rigid_paths g.ground_and_global_sorts with
          | None -> { g with graph }
          | Some (q1,q2) -> raise (EliminationError (CreatesForbiddenPath (q1, q2))) in
     dominance_check g (q1,k,q2)

let merge_constraints src csts g = ElimConstraints.fold (enforce_constraint src) csts g

let check_constraint g (q1, k, q2) = check_func k g.graph q1 q2

let check_constraints csts g = ElimConstraints.for_all (check_constraint g) csts

exception AlreadyDeclared = G.AlreadyDeclared

let add_quality q g =
  let graph = G.add q g.graph in
  let g = enforce_constraint Static (Quality.qtype, ElimConstraint.ElimTo, q) { g with graph } in
  let (paths,ground_and_global_sorts) =
    if Quality.is_qglobal q
    then (RigidPaths.add (Quality.qtype, q) g.rigid_paths, q :: g.ground_and_global_sorts)
    else (g.rigid_paths,g.ground_and_global_sorts) in
  (* As Type ~> s, set Type to be the dominant sort of q if q is a variable. *)
  let dominant = match q with
    | Quality.QVar qv -> QMap.add qv Quality.qtype g.dominant
    | Quality.QConstant _ -> g.dominant in
  { g with rigid_paths = paths; ground_and_global_sorts; dominant }

let check_declared_qualities g l =
  G.check_declared g.graph l

let enforce_eliminates_to src s1 s2 g =
  enforce_constraint src (s1, ElimConstraint.ElimTo, s2) g

let enforce_eq s1 s2 g =
  enforce_constraint Internal (s1, ElimConstraint.Equal, s2) g

let initial_graph =
  let g = G.empty in
  let g = List.fold_left (fun g q -> G.add q g) g Quality.all_constants in
  (* Enforces the constant constraints defined in the table of
     [Constants.eliminates_to] without reflexivity (should be consistent,
     otherwise the [Option.get] will fail). *)
  let fold (g,p) (q,q') =
    if ElimTable.eliminates_to q q'
    then (Option.get @@ G.enforce_lt q q' g, RigidPaths.add (q', q) (RigidPaths.add (q, q') p))
    (* we also add (q', q) as this check is never needed: inserting in the graph
       with Lt ensures that a path between q' and q will be detected as forbidden *)
    else (g,p)
  in
  let (g,p) = List.fold_left fold (g,RigidPaths.empty) @@ non_refl_pairs Quality.all_constants in
  { graph = g;
    rigid_paths = p;
    ground_and_global_sorts = Quality.all_constants;
    dominant = QMap.empty;
    delayed_check = QMap.empty; }

let eliminates_to g q q' =
  check_func ElimConstraint.ElimTo g.graph q q'

let sort_eliminates_to g s1 s2 =
  eliminates_to g (quality s1) (quality s2)

let check_eq g q1 q2 =
  Sorts.Quality.equal q1 q2 ||
    G.check_eq g.graph q1 q2

let check_eq_sort g s s' = check_eq g (quality s) (quality s')

let eliminates_to_prop g q = eliminates_to g q Quality.qprop

let domain g = G.domain g.graph

let qvar_domain g =
  Quality.Set.fold
    (fun q acc -> match q with Quality.QVar q -> QVar.Set.add q acc | _ -> acc)
    (domain g) QVar.Set.empty

let is_empty g = QVar.Set.is_empty (qvar_domain g)

(* Pretty printing *)

let pr_pmap sep pr map =
  let cmp (u,_) (v,_) = Quality.compare u v in
  Pp.prlist_with_sep sep pr (List.sort cmp (Quality.Map.bindings map))

let pr_arc prq =
  let open Pp in
  function
  | u, G.Node ltle ->
    if Quality.Map.is_empty ltle then mt ()
    else
      prq u ++ str " " ++
      v 0
        (pr_pmap spc (fun (v, strict) ->
              (if strict then str "< " else str "<= ") ++ prq v)
            ltle) ++
      fnl ()
  | u, G.Alias v ->
    prq u  ++ str " = " ++ prq v ++ fnl ()


let repr g = G.repr g.graph

let pr_qualities prq g = pr_pmap Pp.mt (pr_arc prq) (repr g)

let explain_quality_inconsistency prv r =
  let open Pp in
  let pr_cst = function
    | AcyclicGraph.Eq -> str"="
    | AcyclicGraph.Le -> str"~>"
    | AcyclicGraph.Lt -> str"~>" (* Yes, it's the same as above. *)
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
       str "because it would identify" ++
         prlist (fun q -> spc() ++ str"and" ++ spc() ++ Quality.pr prv q) constants ++
         spc() ++ str"which is inconsistent." ++ spc() ++
         str"This is introduced by the constraints" ++ spc() ++ Quality.pr prv pstart ++
         prlist (fun (r,v) -> spc() ++ pr_cst r ++ str" " ++ Quality.pr prv v) p
