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

type t = G.t * RigidPaths.t * Quality.t list

type path_explanation = G.explanation Lazy.t

type explanation =
  | Path of path_explanation
  | Other of Pp.t

type quality_inconsistency =
  ((QVar.t -> Pp.t) option) * (ElimConstraint.kind * Quality.t * Quality.t * explanation option)

(* If s can eliminate to s', we want an edge between s and s'.
   In the acyclic graph, it means setting s to be lower or equal than s'.
   This function ensures a uniform behaviour between [check] and [enforce]. *)
let to_graph_cstr k =
  let open ElimConstraint in
  match k with
    | ElimTo -> AcyclicGraph.Le
    | Equal -> AcyclicGraph.Eq

let check_func k =
  let open AcyclicGraph in
  match to_graph_cstr k with
  | Le -> G.check_leq
  | Eq -> G.check_eq
  | Lt -> assert false

let enforce_func k =
  let open AcyclicGraph in
  match to_graph_cstr k with
  | Le -> G.enforce_leq
  | Eq -> G.enforce_eq
  | Lt -> assert false

type constraint_source =
  | Internal
  | Rigid
  | Static

type elimination_error =
  | IllegalConstraint
  | CreatesForbiddenPath of Quality.t * Quality.t
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

let enforce_constraint src (q1,k,q2) (g,p,dom) =
  match enforce_func k q1 q2 g with
  | None ->
     let e = lazy (G.get_explanation (q1,to_graph_cstr k,q2) g) in
     raise @@ EliminationError (QualityInconsistency (None, (k, q1, q2, Some (Path e))))
  | Some g' ->
     match src with
     | Static -> (g',p,dom)
     | Rigid ->
        if (Quality.is_qconst q1 && Quality.is_qconst q2) ||
             (Quality.is_qsprop q1 && not (Quality.is_qsprop q2)) ||
               (Quality.is_qprop q1 && not (Quality.is_qprop q2))
        then raise (EliminationError IllegalConstraint)
        else (g', RigidPaths.add (q1,q2) @@ add_transitive_rigid_paths q1 q2 p,dom)
     | Internal ->
        match get_new_rigid_path g' p dom with
        | None -> (g',p,dom)
        | Some (q1,q2) -> raise (EliminationError (CreatesForbiddenPath (q1, q2)))

let merge_constraints src csts g = ElimConstraints.fold (enforce_constraint src) csts g

let check_constraint (g,_,_) (q1, k, q2) = check_func k g q1 q2

let check_constraints csts g = ElimConstraints.for_all (check_constraint g) csts

exception AlreadyDeclared = G.AlreadyDeclared

let add_quality q (g,p,dom) =
  let g = G.add q g in
  let (g,p,dom) = enforce_constraint Static (Quality.qtype, ElimConstraint.ElimTo, q) (g,p,dom) in
  let (p,dom) = if Quality.is_qglobal q
                then (RigidPaths.add (Quality.qtype, q) p, q :: dom)
                else (p,dom) in
  (g,p,dom)

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
  (g,p,Quality.all_constants)

let eliminates_to (g,_,_) q q' =
  check_func ElimConstraint.ElimTo g q q'

let sort_eliminates_to g s1 s2 =
  eliminates_to g (quality s1) (quality s2)

let check_eq (g,_,_) = G.check_eq g

let check_eq_sort g s s' = check_eq g (quality s) (quality s')

let eliminates_to_prop g q = eliminates_to g q Quality.qprop

let domain (g,_,_) = G.domain g

let qvar_domain g =
  Quality.Set.fold
    (fun q acc -> match q with Quality.QVar q -> QVar.Set.add q acc | _ -> acc)
    (domain g) QVar.Set.empty

let is_empty g = QVar.Set.is_empty (qvar_domain g)

let explain_quality_inconsistency defprv (prv, (k, q1, q2, r)) =
  let open Pp in
  let prv = match prv with None -> defprv | Some prv -> prv in
  let pr_cst = function
    | AcyclicGraph.Eq -> str"="
    | AcyclicGraph.Le -> str"->"
    | AcyclicGraph.Lt -> str"->" (* Yes, it's the same as above. *)
  in
  let reason = match r with
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
  in
  str "Cannot enforce" ++ spc() ++ Quality.pr prv q1 ++ spc() ++
    ElimConstraint.pr_kind k ++ spc() ++ Quality.pr prv q2 ++ spc() ++ reason

let explain_elimination_error defprv err =
  let open Pp in
  match err with
  | IllegalConstraint -> str "This constraint is illegal"
  | CreatesForbiddenPath (q1,q2) ->
     str "This expression would enforce a non-declared elimination constraint between" ++
       spc() ++ Quality.pr defprv q1 ++ spc() ++ str"and" ++ spc() ++ Quality.pr defprv q2
  | QualityInconsistency incon ->
     str"the quality constraints are inconsistent: " ++
       explain_quality_inconsistency defprv incon

module Internal = struct
  let add_template_qvars qvs =
    let set_elim_to_prop v = enforce_eliminates_to Internal (Quality.QVar v) Quality.qprop in
    QVar.Set.fold set_elim_to_prop qvs
end
