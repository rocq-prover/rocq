(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The statement report of [rocqchk -statement-report FILE]: for each
    request, whether a constant has the type of another one, and the axioms
    and relaxed typing flags the first one rests on.

    The closure follows what [Print Assumptions] walks (vernac/assumptions.ml,
    which the checker cannot link): the body and the type of a constant, the
    parameters, arities and constructor types of an inductive block, and, for
    a constant that a module signature leaves without a body, the body that the
    module's implementation gives it. The implementation is read from the
    environment, which keeps the implementation of every module it holds, so
    an object that only the implementation declares is found too, whether its
    library was checked, loaded with -norec, or admitted. *)

open Util
open Names
open Declarations
open Mod_declarations

(** {6 Requests} *)

type request = {
  req_name : string;
  req_model : string;
  req_trusted : string option;
}

let usage_error file lineno =
  CErrors.user_err
    Pp.(str "-statement-report: line " ++ int lineno ++ str " of " ++ str file ++
        str " is not `<name> <model-constant> [<trusted-constant>|-]`.")

(* Tokens are separated by single spaces: two spaces in a row make an empty
   token, which is refused, so no token can contain a space, and a tab or a
   carriage return is refused outright, so no token can split a report line. *)
let parse_line file lineno line =
  if String.exists (fun c -> c = '\t' || c = '\r') line then usage_error file lineno;
  let tokens = String.split_on_char ' ' line in
  if List.exists (fun t -> String.equal t "") tokens then usage_error file lineno;
  match tokens with
  | [name; model] | [name; model; "-"] ->
    { req_name = name; req_model = model; req_trusted = None }
  | [name; model; trusted] ->
    { req_name = name; req_model = model; req_trusted = Some trusted }
  | _ -> usage_error file lineno

let read_requests file =
  let ch =
    try open_in file
    with Sys_error msg ->
      CErrors.user_err Pp.(str "-statement-report: cannot read " ++ str file ++ str ": " ++ str msg)
  in
  let rec loop lineno acc =
    match input_line ch with
    | exception End_of_file -> List.rev acc
    | line when String.equal line "" || line.[0] = '#' -> loop (lineno + 1) acc
    | line -> loop (lineno + 1) (parse_line file lineno line :: acc)
  in
  Fun.protect ~finally:(fun () -> close_in_noerr ch) (fun () -> loop 1 [])

(** {6 Implementations hidden by module signatures}

    A port of [lookup_constant] and [lookup_mind] of vernac/assumptions.ml:
    an object is looked up in the environment, and in the implementation of
    its module when the environment does not hold it or holds it without a
    body. *)

type state = {
  env : Environ.env;
  access : Opaqueproof.opaque -> Opaqueproof.opaque_proofterm;
  mutable fields : structure_body ModPath.Map.t;
  (* the fields of the implementation of each module looked up so far *)
  mutable nodes : node GlobRef.Map.t;
  (* each object reached so far, keyed by its constant or by the first
     inductive of its block *)
  mutable gen : int;
  keys : Constr.t array;
  gens : int array;
  (* the cache of [seen] *)
}

and node = {
  refs : GlobRef.t list;
  (* the objects the declaration mentions *)
  axiom : bool;
  (* no body: a constant without one, an opaque constant whose body cannot be
     read, or an object neither the environment nor an implementation
     resolves, which is reported rather than left out *)
  flags : (string * string) list;
  (* the relaxed typing conditions the object relies on, (kind, object) *)
}

let rec search_label get lab = function
  | [] -> raise Not_found
  | (l, field) :: fields ->
    match get field with
    | Some x when Id.equal l lab -> x
    | _ -> search_label get lab fields

let as_module = function SFBmodule mb -> Some mb | _ -> None
let as_constant = function SFBconst cb -> Some cb | _ -> None
let as_mind = function SFBmind mib -> Some mib | _ -> None

let rec fields_of_functor f subs mp0 args = function
  | NoFunctor a -> f subs mp0 args a
  | MoreFunctor (mbid, _, e) ->
    match args with
    | [] -> raise Not_found (* an unapplied functor has no fields *)
    | mpa :: args ->
      let subs =
        Mod_subst.join (Mod_subst.map_mbid mbid mpa (Mod_subst.empty_delta_resolver mpa)) subs in
      fields_of_functor f subs mp0 args e

let rec lookup_module_in_impl st mp = match mp with
  | MPfile _ | MPbound _ -> Environ.lookup_module mp st.env
  | MPdot (mp', lab) -> search_label as_module lab (fields_of_mp st mp')

and fields_of_mp st mp =
  match ModPath.Map.find_opt mp st.fields with
  | Some fields -> fields
  | None ->
    let mb = lookup_module_in_impl st mp in
    let fields, inner_mp, subs = fields_of_mb st Mod_subst.empty_subst mp mb [] in
    let subs =
      if ModPath.equal inner_mp mp then subs
      else if Mod_subst.has_root_delta_resolver mp (mod_delta mb) then
        Mod_subst.add_mp inner_mp mp (Mod_subst.of_body_delta_resolver (mod_delta mb)) subs
      else Mod_subst.add_mp inner_mp mp (Mod_subst.empty_delta_resolver mp) subs
    in
    let fields = Modops.subst_structure subs mp fields in
    st.fields <- ModPath.Map.add mp fields st.fields;
    fields

and fields_of_mb st subs mp mb args = match mod_expr mb with
  | Algebraic me ->
    fields_of_functor (fields_of_expr st) subs mp args
      (Modops.annotate_module_expression me (mod_type mb))
  | Struct (_, struc) ->
    fields_of_signature subs mp args (Modops.annotate_struct_body struc (mod_type mb))
  | Abstract | FullStruct -> fields_of_signature subs mp args (mod_type mb)

and fields_of_signature subs mp args sign =
  fields_of_functor (fun subs mp0 args struc ->
      if not (List.is_empty args) then raise Not_found;
      (struc, mp0, subs))
    subs mp args sign

and fields_of_expr st subs mp0 args = function
  | MEident mp ->
    let mp = Mod_subst.subst_mp subs mp in
    fields_of_mb st subs mp (lookup_module_in_impl st mp) args
  | MEapply (me, mp) -> fields_of_expr st subs mp0 (mp :: args) me
  | MEwith _ -> raise Not_found (* no 'with' in an implementation *)

let in_impl st get kn =
  let mp, lab = KerName.repr kn in
  try Some (search_label get lab (fields_of_mp st mp)) with Not_found -> None

let lookup_constant st kn =
  if Environ.mem_constant kn st.env then
    let cb = Environ.lookup_constant kn st.env in
    if Declareops.constant_has_body cb then Some cb
    else match in_impl st as_constant (Constant.canonical kn) with
      | Some cb -> Some cb
      | None -> Some cb
  else in_impl st as_constant (Constant.canonical kn)

let lookup_mind st mind =
  if Environ.mem_mind mind st.env then Some (Environ.lookup_mind mind st.env)
  else in_impl st as_mind (MutInd.canonical mind)

(** {6 The objects a declaration mentions} *)

(* A term is a graph with shared nodes: [seen] skips a node already walked in
   the same declaration, as vernac/assumptions.ml does, with a cache of the
   same size. The cache is lossy and direct-mapped: a miss only walks the node
   again. *)
let cache_size = 1 lsl 18

let fresh_gen st = st.gen <- st.gen + 1; st.gen

(* The top of the term, looked at to a bounded depth: shared nodes at the
   same place hash alike without walking the term. *)
let rec hash_top n c =
  let open Hashset.Combine in
  let sub c = if n <= 1 then 0 else hash_top (n - 1) c in
  match Constr.kind c with
  | Const (kn, _) -> combinesmall 1 (Constant.UserOrd.hash kn)
  | Ind ((mi, i), _) -> combinesmall 2 (combine (MutInd.UserOrd.hash mi) i)
  | Construct (((mi, i), j), _) -> combinesmall 3 (combine3 (MutInd.UserOrd.hash mi) i j)
  | Var id -> combinesmall 4 (Id.hash id)
  | Rel i -> combinesmall 5 i
  | App (f, args) ->
    let k = Array.length args in
    combinesmall 6 (combine3 (sub f) k (if Int.equal k 0 then 0 else sub args.(k - 1)))
  | Lambda (_, t, b) -> combinesmall 7 (combine (sub t) (sub b))
  | Prod (_, t, b) -> combinesmall 8 (combine (sub t) (sub b))
  | LetIn (_, b, t, c) -> combinesmall 9 (combine3 (sub b) (sub t) (sub c))
  | Proj (p, _, c) -> combinesmall 10 (combine (Projection.CanOrd.hash p) (sub c))
  | Case (ci, _, _, _, _, c, br) ->
    combinesmall 11 (combine3 (Ind.UserOrd.hash ci.ci_ind) (Array.length br) (sub c))
  | Cast (c, _, _) -> combinesmall 12 (sub c)
  | Fix (_, (_, tl, _)) -> combinesmall 13 (Array.length tl)
  | CoFix (_, (_, tl, _)) -> combinesmall 14 (Array.length tl)
  | Array (_, t, _, _) -> combinesmall 15 (Array.length t)
  | Int i -> combinesmall 16 (Uint63.hash i)
  | Float _ -> 17
  | String _ -> 18
  | Sort _ -> 19
  | Meta i -> combinesmall 20 i
  | Evar _ -> 21

let seen st gen c =
  let i = hash_top 3 c land (cache_size - 1) in
  if Int.equal st.gens.(i) gen && st.keys.(i) == c then true
  else begin
    st.gens.(i) <- gen;
    st.keys.(i) <- c;
    false
  end

let add_mind mind refs = GlobRef.Set.add (GlobRef.IndRef (mind, 0)) refs

(* The walk keeps its own list of terms to visit, so its depth does not depend
   on the depth of the terms. The inductive of a [match] and of a projection
   is an object the term relies on even though no subterm names it. *)
let rec walk st gen refs = function
  | [] -> refs
  | c :: todo ->
    let open Constr in
    match kind c with
    | Rel _ | Var _ | Sort _ | Meta _ | Evar _ | Int _ | Float _ | String _ ->
      walk st gen refs todo
    | Const (kn, _) -> walk st gen (GlobRef.Set.add (GlobRef.ConstRef kn) refs) todo
    | Ind ((mind, _), _) | Construct (((mind, _), _), _) ->
      walk st gen (add_mind mind refs) todo
    | Cast _ | Prod _ | Lambda _ | LetIn _ | App _ | Proj _ | Case _ | Fix _ | CoFix _ | Array _ ->
      if seen st gen c then walk st gen refs todo
      else
        let refs = match kind c with
          | Case (ci, _, _, _, _, _, _) -> add_mind (fst ci.ci_ind) refs
          | Proj (p, _, _) -> add_mind (Projection.mind p) refs
          | _ -> refs
        in
        walk st gen refs (fold (fun todo c -> c :: todo) todo c)

let push_context ctx todo =
  List.fold_left (fun todo d ->
      Context.Rel.Declaration.fold_constr (fun c todo -> c :: todo) d todo)
    todo ctx

let typing_flags name (tf : typing_flags) acc =
  let add ok kind acc = if ok then acc else (kind, name) :: acc in
  acc
  |> add tf.check_universes "type-in-type"
  |> add tf.check_guarded "unsafe-fixpoint"
  |> add tf.check_eliminations "unchecked-eliminations"

(* The same test as vernac/assumptions.ml's [uses_uip]. *)
let uses_uip mib =
  Array.exists (fun mip ->
      Option.is_empty mip.mind_squashed
      && (match mip.mind_relevance with Sorts.Irrelevant -> true | _ -> false)
      && Int.equal (Array.length mip.mind_nf_lc) 1
      && Int.equal (List.length (fst mip.mind_nf_lc.(0))) (List.length mib.mind_params_ctxt))
    mib.mind_packets

let unresolved = { refs = []; axiom = true; flags = [] }

let constant_node st kn =
  match lookup_constant st kn with
  | None -> unresolved
  | Some cb ->
    (* An opaque body that cannot be read is reported as an axiom, as
       vernac/assumptions.ml's [get_constant_body] does. *)
    let body, axiom = match cb.const_body with
      | Def c -> [c], false
      | OpaqueDef o ->
        (match st.access o with
         | c, _ -> [c], false
         | exception e when CErrors.noncritical e -> [], true)
      | Undef _ | Primitive _ | Symbol _ -> [], true
    in
    let refs = walk st (fresh_gen st) GlobRef.Set.empty (cb.const_type :: body) in
    { refs = GlobRef.Set.elements refs; axiom;
      flags = typing_flags (Constant.to_string kn) cb.const_typing_flags [] }

let mind_node st mind =
  match lookup_mind st mind with
  | None -> unresolved
  | Some mib ->
    let todo =
      Array.fold_left (fun todo mip ->
          push_context mip.mind_arity_ctxt
            (Array.fold_left (fun todo c -> c :: todo) todo mip.mind_user_lc))
        (push_context mib.mind_params_ctxt []) mib.mind_packets
    in
    let refs = walk st (fresh_gen st) GlobRef.Set.empty todo in
    let name = MutInd.to_string mind in
    let tf = mib.mind_typing_flags in
    let flags = typing_flags name tf [] in
    let add cond kind flags = if cond then (kind, name) :: flags else flags in
    let flags =
      flags
      |> add (not tf.check_positive) "assumed-positive"
      |> add (uses_uip mib) "uip"
      |> add (not tf.indices_matter
              && Array.exists (fun mip -> mip.mind_relies_on_indices_not_mattering) mib.mind_packets)
        "indices-not-mattering"
    in
    { refs = GlobRef.Set.elements refs; axiom = false; flags }

let node st obj =
  match GlobRef.Map.find_opt obj st.nodes with
  | Some n -> n
  | None ->
    let n = match obj with
      | GlobRef.ConstRef kn -> constant_node st kn
      | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) -> mind_node st mind
      | GlobRef.VarRef _ -> { refs = []; axiom = false; flags = [] }
    in
    st.nodes <- GlobRef.Map.add obj n st.nodes;
    n

let name_of = function
  | GlobRef.ConstRef kn -> Constant.to_string kn
  | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) -> MutInd.to_string mind
  | GlobRef.VarRef id -> Id.to_string id

module FlagSet = Stdlib.Set.Make (struct
    type t = string * string
    let compare (k1, o1) (k2, o2) =
      let c = String.compare k1 k2 in
      if Int.equal c 0 then String.compare o1 o2 else c
  end)

(** The axioms and flags of every object reachable from [root]. *)
let closure st root =
  let rec loop visited axioms flags = function
    | [] -> axioms, flags
    | obj :: todo ->
      if GlobRef.Set.mem obj visited then loop visited axioms flags todo
      else
        let n = node st obj in
        let axioms = if n.axiom then CString.Set.add (name_of obj) axioms else axioms in
        let flags = List.fold_left (fun flags f -> FlagSet.add f flags) flags n.flags in
        loop (GlobRef.Set.add obj visited) axioms flags (List.rev_append n.refs todo)
  in
  loop GlobRef.Set.empty CString.Set.empty FlagSet.empty [root]

(** {6 The type match} *)

(* Whether the model constant HAS the trusted constant's type: conversion, not
   cumulativity, and for polymorphic constants the same check of universe
   contexts as Subtyping makes, in both directions, so that neither side may
   carry a constraint the other does not. *)
let type_verdict env model trusted =
  let cm = Environ.lookup_constant model env and ct = Environ.lookup_constant trusted env in
  let conv env =
    match Conversion.conv env cm.const_type ct.const_type with
    | Result.Ok () -> "match"
    | Result.Error () -> "mismatch"
  in
  match cm.const_universes, ct.const_universes with
  | Monomorphic, Monomorphic -> conv env
  | Polymorphic am, Polymorphic at ->
    if Subtyping.check_polymorphic_universes env at am
    && Subtyping.check_polymorphic_universes env am at
    then conv (Environ.push_context ~strict:false (UVars.AbstractContext.repr at) env)
    else "universes-differ"
  | Monomorphic, Polymorphic _ | Polymorphic _, Monomorphic -> "universes-differ"

(** {6 The report} *)

(* One message per line, so that a long report never builds one [Pp.t]. *)
let line fmt = Printf.ksprintf (fun s -> Feedback.msg_notice (Pp.str s)) fmt

let print env access requests =
  let index =
    Environ.fold_constants (fun c _ acc -> CString.Map.add (Constant.to_string c) c acc)
      env CString.Map.empty
  in
  let st = {
    env; access; fields = ModPath.Map.empty; nodes = GlobRef.Map.empty; gen = 0;
    keys = Array.make cache_size Constr.mkProp; gens = Array.make cache_size (-1);
  } in
  line "STATEMENT REPORT";
  List.iter (fun r ->
      let trusted = Option.default "-" r.req_trusted in
      match CString.Map.find_opt r.req_model index with
      | None -> line "statement %s %s %s model-missing 0 0" r.req_name r.req_model trusted
      | Some model ->
        let axioms, flags = closure st (GlobRef.ConstRef model) in
        let verdict = match r.req_trusted with
          | None -> "not-requested"
          | Some t ->
            match CString.Map.find_opt t index with
            | None -> "trusted-missing"
            | Some t -> type_verdict env model t
        in
        line "statement %s %s %s %s %d %d" r.req_name r.req_model trusted verdict
          (CString.Set.cardinal axioms) (FlagSet.cardinal flags);
        CString.Set.iter (line "axiom %s %s" r.req_name) axioms;
        FlagSet.iter (fun (kind, obj) -> line "flag %s %s %s" r.req_name kind obj) flags)
    requests;
  line "END STATEMENT REPORT"
