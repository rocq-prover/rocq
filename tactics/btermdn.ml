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
open Constr
open Names
open Pattern

let debug = CDebug.create ~name:"dnet-decomp" ()

(* Discrimination nets with bounded depth.
   See the module dn.ml for further explanations.
   Eduardo (5/8/97). *)

let dnet_depth = ref 8

type term_label =
| GRLabel of GlobRef.t
| ProjLabel of Projection.Repr.t * int
 (** [ProjLabel (p, n)] represents a possibly partially applied projection [p]
     with [n] arguments missing to be fully applied. [n] is always zero for
     labels derived from [Proj] terms but can be greater than zero for labels
     derived from compatibility constants. *)
| ProdLabel
| SortLabel
| CaseLabel
| LamLabel

let compare_term_label t1 t2 = match t1, t2 with
| GRLabel gr1, GRLabel gr2 -> GlobRef.UserOrd.compare gr1 gr2
| ProjLabel (p1, n1), ProjLabel (p2, n2) ->
  let c = Int.compare n1 n2 in
  if c <> 0 then c else
    (Projection.Repr.UserOrd.compare p1 p2)
| _ -> Stdlib.compare t1 t2 (** OK *)

let pr_term_label (l : term_label) =
  let open Pp in
  match l with
  | GRLabel gr ->
    str "GRLabel(" ++ GlobRef.print gr ++ str ")"
  | ProjLabel (proj, i) ->
    str "ProjLabel(" ++ Projection.Repr.print proj ++ str ", " ++ int i ++ str ")"
  | ProdLabel -> str "ProdLabel"
  | SortLabel -> str "SortLabel"
  | CaseLabel -> str "CaseLabel"
  | LamLabel -> str "LamLabel"

type 'res lookup_res = 'res Dn.lookup_res = Label of 'res | Nothing | Everything

let pr_lookup_res pr_res r =
  let open Pp in
  match r with
  | Label lbl ->
    str "Label(" ++ hv 2 (pr_res lbl) ++ str ")"
  | Nothing -> str "Nothing"
  | Everything -> str "Everything"


(* let eta_reduce = Reductionops.shrink_eta *)

let evaluable_constant c env ts =
  (* This is a hack to work around a broken Print Module implementation, see
     bug #2668. *)
  (if Environ.mem_constant c env then Environ.evaluable_constant c env else true) &&
  (match ts with None -> true | Some ts -> Structures.PrimitiveProjections.is_transparent_constant ts c)

let evaluable_named id env ts =
  (try Environ.evaluable_named id env with Not_found -> true) &&
  (match ts with None -> true | Some ts -> TransparentState.is_transparent_variable ts id)

let evaluable_projection p _env ts =
  (match ts with None -> true | Some ts -> TransparentState.is_transparent_projection ts (Projection.repr p))

let label_of_opaque_constant c stack =
  match Structures.PrimitiveProjections.find_opt c with
  | None -> (GRLabel (ConstRef c), stack)
  | Some p ->
    let n_args_needed = Structures.Structure.projection_nparams c + 1 in (* +1 for the record value itself *)
    let n_args_given = List.length stack in
    let n_args_missing = max (n_args_needed - n_args_given) 0 in
    let n_args_drop = min (n_args_needed - 1) n_args_given in (* we do not drop the record value from the stack *)
    (ProjLabel (p, n_args_missing), List.skipn n_args_drop stack)

type constr_res = (term_label * partial_constr list) lookup_res
and partial_constr =
  | Constr of EConstr.t
  | PartialConstr of constr_res

let rec pr_constr_res pr_constr (cr : constr_res) =
  let open Pp in
  let pr_partial_constr (pc : partial_constr) =
    match pc with
    | Constr c ->
      str "Constr(" ++ hv 2 (pr_constr c) ++ str ")"
    | PartialConstr pc ->
      str "PartialConstr([" ++ hv 2 (pr_constr_res pr_constr pc) ++ str "])"
  in
  let aux (lbl, pcs) =
    pr_term_label lbl ++
    str "," ++
    prlist_with_sep
      (fun () -> str ",")
      pr_partial_constr
      pcs
  in
  pr_lookup_res aux cr

let decomp_lambda_constr sigma decomp : EConstr.t list -> EConstr.t -> constr_res =
  let res ty ds p =
    let acc = Label (LamLabel, [Constr ty; Constr p]) in
    let fn acc ty = (Label (LamLabel, [Constr ty; PartialConstr acc])) in
    let res = List.fold_left fn acc ds in
    res
  in
  let rec go ds p  : constr_res =
    match EConstr.kind sigma p with
    | Lambda (_, ty, c) ->
      let ds = ty :: ds in
      go ds c
    | App (f, args) ->
      let numd = List.length ds in
      let nargs = Array.length args in
      assert (numd > 0);
      let n = min numd nargs in
      (* Feedback.msg_debug Pp.(str "numd: " ++ int numd ++ str ", nargs: " ++ int nargs ++ str ", n: " ++ int n); *)
      let ds = List.skipn n ds in
      let (args, _) = Array.chop (nargs - n) args in
      (* Feedback.msg_debug Pp.(str "constr before: " ++ Printer.pr_econstr_env (Global.env()) sigma p); *)
      let p = EConstr.mkApp (f, args) in
      let p = EConstr.Vars.lift (-n) p in
      (* Feedback.msg_debug Pp.(str "constr after : " ++ Printer.pr_econstr_env (Global.env()) sigma p); *)
      begin
        match decomp [] p, ds with
        | _ as c, [] ->
          c (* no more remaining lambdas  *)
        | Label _, ty :: ds ->
          res ty ds p
        | Nothing, _ | Everything, _ -> Everything
      end
    | _ ->
      begin
        match decomp [] p, ds with
        | _, [] -> assert false
        | Label _, ty :: ds ->
          (* there are left-over lambdas and the body is discriminating *)
          res ty ds p
        | Nothing, _ | Everything, _ -> Everything
      end
  in
  go

(* The pattern view functions below try to overapproximate βι-neutral terms up
   to η-conversion. Some historical design choices are still incorrect w.r.t. to
   this specification. TODO: try to make them follow the spec. *)
let constr_val_discr env sigma ts t : constr_res =
  (* Should we perform weak βι here? *)
  let open GlobRef in
  let rec decomp (stack : partial_constr list) (t : EConstr.t) : constr_res =
    debug Pp.(fun () -> str "constr_val_discr.decomp input: " ++ Printer.pr_leconstr_env env Evd.empty t);
    let out = match EConstr.kind sigma t with
    | App (f,l) -> decomp (Array.fold_right (fun a l -> Constr a :: l) l stack) f
    | Proj (p,_,c) when evaluable_projection p env ts -> Everything
    | Proj (p,_,c) ->
      let p = Environ.QProjection.canonize env p in
      Label(ProjLabel (Projection.repr p, 0), Constr c :: stack)
    | Cast (c,_,_) -> decomp stack c
    | Const (c,_) when evaluable_constant c env ts -> Everything
    | Const (c,_) ->
      let c = Environ.QConstant.canonize env c in
      Label (label_of_opaque_constant c stack)
    | Ind (ind_sp,_) ->
      let ind_sp = Environ.QInd.canonize env ind_sp in
      Label(GRLabel (IndRef ind_sp), stack)
    | Construct (cstr_sp,_) ->
      let cstr_sp = Environ.QConstruct.canonize env cstr_sp in
      Label(GRLabel (ConstructRef cstr_sp), stack)
    | Var id when evaluable_named id env ts -> Everything
    | Var id -> Label(GRLabel (VarRef id), stack)
    | Prod (n,d,c) -> Label(ProdLabel, [Constr d; Constr c])
    | Lambda (_,d,c) when List.is_empty stack ->
      decomp_lambda_constr sigma decomp [d] c
    | Lambda _ -> Everything
    | Sort _ -> Label(SortLabel, [])
    | Evar _ -> Everything
    | Case (_, _, _, _, _, c, _) ->
      begin
        match decomp stack c with
        | Label (GRLabel (ConstructRef _), _) -> Everything (* over-approximating w.r.t. [fMATCH] *)
        | (Label _ | Nothing) as res -> Label(CaseLabel, PartialConstr res :: stack)
        | Everything -> Everything
      end
    | Rel _ | Meta _ | LetIn _ | Fix _ | CoFix _
    | Int _ | Float _ | String _ | Array _ -> Nothing
    in
    debug Pp.(fun () -> str "constr_val_discr.decomp output: " ++ pr_constr_res (Printer.pr_leconstr_env env Evd.empty) out);
    out
  and decomp_partial (stack : partial_constr list) (t : partial_constr) : constr_res =
    match t with
    | Constr t -> decomp stack t
    | PartialConstr res -> res
  in
  decomp_partial [] t

type pat_res = (term_label * partial_pat list) option
and partial_pat =
  | Pattern of constr_pattern
  | PartialPat of pat_res

let rec pr_pat_res pr_pat (cr : pat_res) =
  let open Pp in
  let pr_partial_pat (pc : partial_pat) =
    match pc with
    | Pattern c ->
      str "Pattern(" ++ hv 2 (pr_pat c) ++ str ")"
    | PartialPat pc ->
      str "PartialPat([" ++ hv 2 (pr_pat_res pr_pat pc) ++ str "])"
  in
  let aux (lbl, pcs) =
    pr_term_label lbl ++
    str "," ++
    prlist_with_sep
      (fun () -> str ",")
      pr_partial_pat
      pcs
  in
  match cr with
  | Some x -> str "Some(" ++ hv 2 (aux x) ++ str ")"
  | None -> str "None"

let decomp_lambda_pat decomp : constr_pattern list -> constr_pattern -> pat_res =
  let res ty ds p =
    let acc = Some (LamLabel, [Pattern ty; Pattern p]) in
    let fn acc ty = Some (LamLabel, [Pattern ty; PartialPat acc]) in
    let res = List.fold_left fn acc ds in
    res
  in
  let rec go ds p =
    match p with
    | PLambda (_, ty, c) ->
      let ds = ty :: ds in
      go ds c
    | PApp (f, args) ->
      let numd = List.length ds in
      let nargs = Array.length args in
      assert (numd > 0);
      let n = min numd nargs in
      (* Feedback.msg_debug Pp.(str "numd: " ++ int numd ++ str ", nargs: " ++ int nargs ++ str ", n: " ++ int n); *)
      let ds = List.skipn n ds in
      let (args, _) = Array.chop (nargs - n) args in
      (* Feedback.msg_debug Pp.(str "pattern before:" ++ Printer.pr_constr_pattern_env (Global.env()) (Evd.empty) p); *)
      let p = PApp (f, args) in
      let p = Patternops.lift_pattern (-n) p in
      (* Feedback.msg_debug Pp.(str "pattern after :" ++ Printer.pr_constr_pattern_env (Global.env()) (Evd.empty) p); *)
      begin
        match decomp [] p, ds with
        | _ as c, [] ->
          c (* no more remaining lambdas  *)
        | Some _, ty :: ds ->
          (* there are left-over lambdas and the body is discriminating *)
          res ty ds p
        | None, _ -> None
      end
    | _ ->
      begin
        match decomp [] p, ds with
        | _, [] -> assert false
        | Some _, ty :: ds ->
          (* there are left-over lambdas and the body is discriminating *)
          res ty ds p
        | None, _ -> None
      end
  in
  go


let constr_pat_discr env ts p : pat_res =
  let open GlobRef in
  let rec decomp (stack : partial_pat list) (p : constr_pattern) : pat_res =
    debug Pp.(fun () -> str "constr_pat_discr.decomp input: " ++ Printer.pr_lconstr_pattern_env env Evd.empty p);
    let out = match p with
    | PApp (f,args) -> decomp ((Array.map_to_list (fun p -> Pattern p) args) @ stack) f
    | PProj (p,c) when evaluable_projection p env ts -> None
    | PProj (p,c) ->
      let p = Environ.QProjection.canonize env p in
      Some (ProjLabel (Projection.repr p, 0), Pattern c :: stack)
    | PRef ((IndRef _) as ref)
    | PRef ((ConstructRef _ ) as ref) ->
      let ref = Environ.QGlobRef.canonize env ref in
      Some (GRLabel ref, stack)
    | PRef (VarRef v) when evaluable_named v env ts -> None
    | PRef ((VarRef _) as ref) -> Some (GRLabel ref, stack)
    | PRef (ConstRef c) when evaluable_constant c env ts -> None
    | PRef (ConstRef c) ->
      let c = Environ.QConstant.canonize env c in
      Some (label_of_opaque_constant c stack)
    | PVar v when evaluable_named v env ts -> None
    | PVar v -> Some (GRLabel (VarRef v), stack)
    | PProd (_,d,c) when stack = [] -> Some (ProdLabel, [Pattern d ; Pattern c])
    | PLambda (_,d,c) when List.is_empty stack ->
      decomp_lambda_pat decomp [d] c
    | PSort s when stack = [] -> Some (SortLabel, [])
    | PCase(_,_,p,_) | PIf(p,_,_) ->
      begin
        match decomp stack p with
        | Some (GRLabel (ConstructRef _), _) -> None (* over-approximating w.r.t. [fMATCH] *)
        | Some _ as res -> Some (CaseLabel, PartialPat res :: stack)
        | None -> None
      end
    | _ -> None
    in
    debug Pp.(fun () -> str "constr_pat_discr.decomp output: " ++ pr_pat_res (Printer.pr_lconstr_pattern_env env Evd.empty) out);
    out
  and decomp_partial (stack : partial_pat list) (t : partial_pat) : pat_res =
    match t with
    | Pattern p ->
      decomp stack p
    | PartialPat res -> res
  in
  decomp_partial [] p

let constr_pat_discr_syntactic env p =
  let open GlobRef in
  let rec decomp (stack : partial_pat list) (p : constr_pattern) : pat_res =
    debug Pp.(fun () -> str "constr_pat_discr_syntactic.decomp input: " ++ Printer.pr_lconstr_pattern_env env Evd.empty p);
    let out = match p with
    | PApp (f,args) -> decomp ((Array.map_to_list (fun p -> Pattern p) args) @ stack) f
    | PProj (p,c) ->
      let p = Environ.QProjection.canonize env p in
      Some (ProjLabel (Names.Projection.repr p, 0), Pattern c :: stack)
    | PRef ((IndRef _) as ref)
    | PRef ((ConstructRef _ ) as ref) ->
      let ref = Environ.QGlobRef.canonize env ref in
      Some (GRLabel ref, stack)
    | PRef ((VarRef _) as ref) -> Some (GRLabel ref, stack)
    | PRef (ConstRef c) ->
      let c = Environ.QConstant.canonize env c in
      Some (label_of_opaque_constant c stack)
    | PVar v -> Some (GRLabel (VarRef v), stack)
    | PProd (_,d,c) when stack = [] -> Some (ProdLabel, [Pattern d ; Pattern c])
    | PLambda (_,d,c) when List.is_empty stack ->
      Some (LamLabel, Pattern d :: Pattern c :: stack)
    | PSort s when stack = [] -> Some (SortLabel, [])
    | PCase(_,_,p,_) | PIf(p,_,_) -> Some (CaseLabel, Pattern p :: stack)
    | _ -> None
    in
    debug Pp.(fun () -> str "constr_pat_discr_syntactic.decomp output: " ++ pr_pat_res (Printer.pr_lconstr_pattern_env env Evd.empty) out);
    out
  and decomp_partial (stack : partial_pat list) (t : partial_pat) : pat_res =
    match t with
    | Pattern p -> decomp stack p
    | PartialPat res -> res
  in
  decomp_partial [] p

let bounded_constr_pat_discr env st (t,depth) =
  if Int.equal depth 0 then None
  else match constr_pat_discr env st t with
  | None -> None
  | Some (c,l) -> Some(c,List.map (fun c -> (c,depth-1)) l)

let bounded_constr_pat_discr_syntactic env (t,depth) =
  if Int.equal depth 0 then None
  else match constr_pat_discr_syntactic env t with
  | None -> None
  | Some (c,l) -> Some(c,List.map (fun c -> (c,depth-1)) l)

let bounded_constr_val_discr env st sigma (t,depth) =
  if Int.equal depth 0 then
    Nothing
  else match constr_val_discr env sigma st t with
  | Label (c,l) -> Label(c,List.map (fun c -> (c,depth-1)) l)
  | Nothing -> Nothing
  | Everything -> Everything

module Make =
  functor (Z : Map.OrderedType) ->
struct

 module Y = struct
    type t = term_label
    let compare = compare_term_label
 end

 module Dn = Dn.Make(Y)(Z)

 type t = Dn.t

  type pattern = Dn.pattern

  let pattern env st pat =
    Dn.pattern (bounded_constr_pat_discr env st) (Pattern pat, !dnet_depth)

  let pattern_syntactic env pat =
    Dn.pattern (bounded_constr_pat_discr_syntactic env) (Pattern pat, !dnet_depth)

  let constr_pattern env sigma st pat =
    let mk p = match bounded_constr_val_discr env st sigma p with
    | Label l -> Some l
    | Everything | Nothing -> None
    in
    Dn.pattern mk (Constr pat, !dnet_depth)

  let empty = Dn.empty
  let add = Dn.add
  let rmv = Dn.rmv

  let lookup env sigma st dn t =
    Dn.lookup dn (bounded_constr_val_discr env st sigma) (Constr t,!dnet_depth)

end
