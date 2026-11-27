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
  (match ts with None -> true | Some ts -> TransparentState.is_transparent_projection ts p)

let decomp_constant (c : Names.Constant.t) (args : 'a list) :
  (Names.Projection.Repr.t * int) option * 'a list =
  match Structures.PrimitiveProjections.find_opt c with
  | None -> (None, args)
  | Some p ->
    let n_args_needed = Names.Projection.Repr.npars p + 1 in (* +1 for the record value itself *)
    let n_args_given = List.length args in
    let n_args_missing = max (n_args_needed - n_args_given) 0 in
    let n_args_drop = min (n_args_needed - 1) n_args_given in (* we do not drop the record value from the stack *)
    (Some (p, n_args_missing), List.skipn n_args_drop args)

let label_of_opaque_constant c stack =
  match decomp_constant c stack with
  | (None, stack) -> (GRLabel (ConstRef c), stack)
  | (Some (p, i), stack) -> (ProjLabel (p,i), stack)

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

let decomp_lambda_constr env sigma ts decomp : EConstr.t -> EConstr.t -> constr_res =
  let res ds p =
    match ds with
    | [] -> assert false
    | ty :: ds ->
      let acc = Label (LamLabel, [Constr ty; p]) in
      let fn acc ty = (Label (LamLabel, [Constr ty; PartialConstr acc])) in
      let res = List.fold_left fn acc ds in
      res
  in
  let rec decomp_app c stack =
    let k = EConstr.kind sigma c in
    match k with
    | App (f, args) -> decomp_app f (Array.to_list args @ stack)
    | Const (c, _) -> (k, decomp_constant c stack)
    | Proj (p, b, c) -> (k, (Some (Projection.repr p, 0), c :: stack))
    | _ -> (k, (None, stack))
  in
  let rec go numds ds p  : constr_res =
    match decomp_app p [] with
    | (Lambda (_, ty, c), (None, [])) ->
      let ds = ty :: ds in
      go (numds + 1) ds c
    | (_, (None, [])) ->        (* this is neither a lambda nor an application *)
      begin
        match decomp [] p with
        | _ when ds = [] -> assert false
        | Label _ ->
          (* there are left-over lambdas and the body is discriminating *)
          res ds (Constr p)
        | Nothing | Everything -> Everything
      end
    | (_ as f, (None, args)) -> (* this is an application whose head [f] is not a projection *)
      let nargs = List.length args in
      let n = min numds nargs in
      let ds = List.skipn n ds in
      let args = List.firstn (nargs - n) args in
      let p = EConstr.mkApp (EConstr.of_kind f, Array.of_list args) in
      let p = EConstr.Vars.lift (-n) p in
      begin
        match decomp [] p with
        | _ as c when ds = [] ->
          c (* no more remaining lambdas  *)
        | Label _ -> res ds (Constr p)
        | Nothing | Everything -> Everything
      end
    | (_, (Some (p, _), _)) when evaluable_projection p env ts ->
      Everything
    | (_, (Some (p, args_missing), args)) ->
      (* We have [num_params + |args| - args_missing] virtual arguments left. *)
      let params = Projection.Repr.npars p in
      let nargs = List.length args in
      let total_nargs = params + nargs - args_missing in
      let n = min numds total_nargs in
      let ds = List.skipn n ds in
      let args = List.firstn (max 0 (nargs - n)) args in
      let args = List.map (fun c -> Constr c) args in
      let args_missing = args_missing + (max 0 (n - nargs)) in
      let p = Label (ProjLabel (p, args_missing), args) in
      begin
        match ds with
        | [] -> p
        | _ -> res ds (PartialConstr p)
      end
  in
  fun ty -> go 1 [ty]

(* The pattern view functions below try to overapproximate βι-neutral terms up
   to η-conversion. Some historical design choices are still incorrect w.r.t. to
   this specification. TODO: try to make them follow the spec. *)
let unfold_flags ts =
  let ts = match ts with None -> TransparentState.full | Some ts -> ts in
  RedFlags.red_add_transparent
    RedFlags.(mkflags [fBETA; fDELTA; fZETA]) ts

(* Head of a transparent constant body, reduced under its lambdas. Only heads
   no conversion can unfold become labels, as e.g. auto converts closed terms
   with full transparency. *)
type summ =
| SStar
| SRigid of term_label * summ list
| SArg of int * int
| SProj of Projection.Repr.t * summ * int

let summ_depth = 4

let rec summarize env sigma ts n depth t =
  if Int.equal depth 0 then SStar else
  let t =
    try Reductionops.clos_whd_flags (unfold_flags ts) env sigma t
    with e when CErrors.noncritical e -> t
  in
  let h, args = EConstr.decompose_app sigma t in
  let nargs = Array.length args in
  let sub a = summarize env sigma ts n (depth - 1) a in
  let subs l = List.map sub l in
  let open GlobRef in
  match EConstr.kind sigma h with
  | Rel k when k <= n -> SArg (n - k, nargs)
  | Construct (c, _) ->
    SRigid (GRLabel (ConstructRef (Environ.QConstruct.canonize env c)), subs (Array.to_list args))
  | Ind (i, _) ->
    SRigid (GRLabel (IndRef (Environ.QInd.canonize env i)), subs (Array.to_list args))
  | Const (c, _) when not (evaluable_constant c env ts) ->
    begin match (Environ.lookup_constant c env).Declarations.const_body with
    | Declarations.Undef _ | Declarations.OpaqueDef _ ->
      let c = Environ.QConstant.canonize env c in
      let lbl, rest = label_of_opaque_constant c (Array.to_list args) in
      SRigid (lbl, subs rest)
    | Declarations.Def _ | Declarations.Primitive _ | Declarations.Symbol _ -> SStar
    | exception Not_found -> SStar
    end
  | Var id when not (evaluable_named id env ts) ->
    begin match Environ.lookup_named id env with
    | Context.Named.Declaration.LocalAssum _ -> SRigid (GRLabel (VarRef id), subs (Array.to_list args))
    | Context.Named.Declaration.LocalDef _ -> SStar
    | exception Not_found -> SStar
    end
  | Sort _ when Int.equal nargs 0 -> SRigid (SortLabel, [])
  | Prod (_, d, _) when Int.equal nargs 0 -> SRigid (ProdLabel, [sub d; SStar])
  | Proj (p, _, c) ->
    if evaluable_projection (Projection.repr p) env ts then
      SProj (Projection.repr p, sub c, nargs)
    else SStar
  | _ -> SStar

let is_eta_constructor env = function
| GRLabel (GlobRef.ConstructRef ((mind, i), _)) ->
  let mib = Environ.lookup_mind mind env in
  begin match mib.Declarations.mind_packets.(i).Declarations.mind_record with
  | Declarations.PrimRecord _ -> mib.Declarations.mind_finite == Declarations.BiFinite
  | Declarations.NotRecord | Declarations.FakeRecord -> false
  end
| _ -> false

(* One per hint database and transparent state. Entries are checked against
   the constant body, which closing a section changes in place. *)
type cache = (Declarations.constant_body * int * summ) Environ.QConstant.Map.t ref

let empty_cache () = ref Environ.QConstant.Map.empty

(* Heads labelled by the syntactic patterns (Hint Extern) of a dnet: goals
   keep wildcards for them, since such patterns match them rigidly. *)
type syntactic = {
  syn_consts : unit Environ.QConstant.Map.t;
  syn_projs : unit Environ.QProjection.Repr.Map.t;
}

let empty_syntactic = {
  syn_consts = Environ.QConstant.Map.empty;
  syn_projs = Environ.QProjection.Repr.Map.empty;
}

let is_syntactic_const env syn c =
  Environ.QConstant.Map.mem env c syn.syn_consts ||
  match Structures.PrimitiveProjections.find_opt c with
  | Some p -> Environ.QProjection.Repr.Map.mem env p syn.syn_projs
  | None -> false

let const_summary env sigma ts cache c =
  match Environ.lookup_constant c env with
  | exception Not_found -> (0, SStar)
  | cb ->
  match Environ.QConstant.Map.find_opt env c !cache with
  | Some (cb', n, s) when cb' == cb -> (n, s)
  | _ ->
    let (n, s) as ans = match cb.Declarations.const_body with
    | Declarations.Def b ->
      let b = EConstr.of_constr b in
      let rec strip env n b = match EConstr.kind sigma b with
      | Lambda (na, ty, b) ->
        strip (EConstr.push_rel (Context.Rel.Declaration.LocalAssum (na, ty)) env) (n + 1) b
      | _ -> (env, n, b)
      in
      let env', n, body = strip env 0 b in
      (n, summarize env' sigma ts n summ_depth body)
    | _ -> (0, SStar)
    in
    let () = cache := Environ.QConstant.Map.add env c (cb, n, s) !cache in
    ans

let constr_val_discr env sigma ts cache syn t : constr_res =
  (* Should we perform weak βι here? *)
  let open GlobRef in
  let rec stars k = List.init k (fun _ -> PartialConstr Everything)
  and decomp_with stack pc = match pc with
  | Constr t -> decomp stack t
  | PartialConstr r -> if List.is_empty stack then r else Everything
  and child args s = match s with
  | SArg (j, 0) -> args.(j)
  | _ -> PartialConstr (eval args [] s)
  and eval args extra s = match s with
  | SStar -> Everything
  | SRigid (l, _) when is_eta_constructor env l -> Everything
  | SRigid (l, ch) -> Label (l, List.map (child args) ch @ extra)
  | SArg (j, k) -> decomp_with (stars k @ extra) args.(j)
  | SProj (p, s', k) ->
    begin match field_of_summ p args s' with
    | Some pc -> decomp_with (stars k @ extra) pc
    | None -> Everything
    end
  and field_index p = Projection.Repr.npars p + Projection.Repr.arg p
  and field_of_summ p args s = match s with
  | SArg (j, 0) -> field_of_partial p args.(j)
  | SRigid (GRLabel (ConstructRef _), ch) ->
    Option.map (child args) (List.nth_opt ch (field_index p))
  | _ -> None
  and field_of_partial p pc = match pc with
  | PartialConstr _ -> None
  | Constr t ->
    let h, a = EConstr.decompose_app sigma t in
    match EConstr.kind sigma h with
    | Construct _ ->
      let i = field_index p in
      if i < Array.length a then Some (Constr a.(i)) else None
    | Const (d, _) when evaluable_constant d env ts ->
      let n, s = const_summary env sigma ts cache d in
      if Array.length a < n then None
      else
        let dargs = Array.map (fun x -> Constr x) (Array.sub a 0 n) in
        field_of_summ p dargs s
    | _ -> None
  and summary_const c stack =
    if is_syntactic_const env syn c then Everything
    else
      let n, s = const_summary env sigma ts cache c in
      if List.length stack < n then Everything
      else
        let args = Array.of_list (List.firstn n stack) in
        eval args (List.skipn n stack) s
  and summary_proj p c stack =
    if Environ.QProjection.Repr.Map.mem env p syn.syn_projs then Everything
    else match field_of_partial p (Constr c) with
    | Some pc -> decomp_with stack pc
    | None -> Everything
  and decomp (stack : partial_constr list) (t : EConstr.t) : constr_res =
    debug Pp.(fun () -> str "constr_val_discr.decomp input: " ++ Printer.pr_leconstr_env env sigma t);
    let out = match EConstr.kind sigma t with
    | App (f,l) -> decomp (Array.fold_right (fun a l -> Constr a :: l) l stack) f
    | Proj (p,_,c) when evaluable_projection (Projection.repr p) env ts -> summary_proj (Projection.repr p) c stack
    | Proj (p,_,c) ->
      let p = Environ.QProjection.canonize env p in
      Label(ProjLabel (Projection.repr p, 0), Constr c :: stack)
    | Cast (c,_,_) -> decomp stack c
    | Const (c,_) when evaluable_constant c env ts -> summary_const c stack
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
      decomp_lambda_constr env sigma ts decomp d c
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
    debug Pp.(fun () -> str "constr_val_discr.decomp output: " ++ pr_constr_res (Printer.pr_leconstr_env env sigma) out);
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

let decomp_lambda_pat env ts decomp : constr_pattern -> constr_pattern -> pat_res =
  let res ds p =
    match ds with
    | [] -> assert false
    | ty :: ds ->
      let acc = Some (LamLabel, [Pattern ty; p]) in
      let fn acc ty = Some (LamLabel, [Pattern ty; PartialPat acc]) in
      let res = List.fold_left fn acc ds in
      res
  in
  let rec decomp_app p stack =
    match p with
    | PApp (f, args) -> decomp_app f (Array.to_list args @ stack)
    | PRef (ConstRef c) -> (p, decomp_constant c stack)
    | PProj (pr, c) -> (p, (Some (Projection.repr pr, 0), c :: stack))
    | _ -> (p, (None, stack))
  in
  let rec go numds ds p  : pat_res =
    match decomp_app p [] with
    | (PLambda (_, ty, c), (None, [])) ->
      let ds = ty :: ds in
      go (numds + 1) ds c
    | (_, (None, [])) ->        (* this is neither a lambda nor an application *)
      begin
        match decomp [] p with
        | _ when ds = [] -> assert false
        | Some _ ->
          (* there are left-over lambdas and the body is discriminating *)
          res ds (Pattern p)
        | None -> None
      end
    | (_ as f, (None, args)) -> (* this is an application whose head [f] is not a projection *)
      let nargs = List.length args in
      let n = min numds nargs in
      let ds = List.skipn n ds in
      let args = List.firstn (nargs - n) args in
      let p = PApp (f, Array.of_list args) in
      let p = Patternops.lift_pattern (-n) p in
      begin
        match decomp [] p with
        | _ as c when ds = [] ->
          c (* no more remaining lambdas  *)
        | Some _ ->
          (* there are left-over lambdas and the body is discriminating *)
          res ds (Pattern p)
        | None -> None
      end
    | (_, (Some (p, _), _)) when evaluable_projection p env ts ->
      None
    | (_, (Some (p, args_missing), args)) ->
      (* We have [num_params + |args| - args_missing] virtual arguments left. *)
      let params = Projection.Repr.npars p in
      let nargs = List.length args in
      let total_nargs = params + nargs - args_missing in
      let n = min numds total_nargs in
      let ds = List.skipn n ds in
      let args = List.firstn (max 0 (nargs - n)) args in
      let args = List.map (fun c -> Pattern c) args in
      let args_missing = args_missing + (max 0 (n - nargs)) in
      let p = (Some (ProjLabel (p, args_missing), args)) in
      begin
        match ds with
        | [] -> p
        | _ -> res ds (PartialPat p)
      end
  in
  fun ty -> go 1 [ty]


let constr_pat_discr env ts p : pat_res =
  let open GlobRef in
  let rec decomp (stack : partial_pat list) (p : constr_pattern) : pat_res =
    debug Pp.(fun () -> str "constr_pat_discr.decomp input: " ++ Printer.pr_lconstr_pattern_env env Evd.empty p);
    let out = match p with
    | PApp (f,args) -> decomp ((Array.map_to_list (fun p -> Pattern p) args) @ stack) f
    | PProj (p,c) when evaluable_projection (Projection.repr p) env ts -> None
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
      decomp_lambda_pat env ts decomp d c
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
      decomp_lambda_pat env (Some TransparentState.full) decomp d c
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

let bounded_constr_val_discr env st sigma cache syn (t,depth) =
  if Int.equal depth 0 then
    Nothing
  else match constr_val_discr env sigma st cache syn t with
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

  let pattern_syntactic env syn pat =
    let syn = ref syn in
    let record p = match bounded_constr_pat_discr_syntactic env p with
      | Some (GRLabel (GlobRef.ConstRef c), _) as r ->
        let () = syn := { !syn with syn_consts = Environ.QConstant.Map.add env c () !syn.syn_consts } in
        r
      | Some (ProjLabel (pr, _), _) as r ->
        let () = syn := { !syn with syn_projs = Environ.QProjection.Repr.Map.add env pr () !syn.syn_projs } in
        r
      | r -> r
    in
    let pat = Dn.pattern record (Pattern pat, !dnet_depth) in
    !syn, pat

  let constr_pattern env sigma cache st pat =
    let mk p = match bounded_constr_val_discr env st sigma cache empty_syntactic p with
    | Label l -> Some l
    | Everything | Nothing -> None
    in
    Dn.pattern mk (Constr pat, !dnet_depth)

  let empty = Dn.empty
  let add = Dn.add
  let rmv = Dn.rmv

  let lookup env sigma cache syn st dn t =
    Dn.lookup dn (bounded_constr_val_discr env st sigma cache syn) (Constr t,!dnet_depth)

end
