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
   token, which is refused, so no token can contain a space. *)
let parse_line file lineno line =
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
    | line ->
      if String.exists (fun c -> c = '\t' || c = '\r') line then usage_error file lineno;
      if String.equal line "" || line.[0] = '#' then loop (lineno + 1) acc
      else loop (lineno + 1) (parse_line file lineno line :: acc)
  in
  Fun.protect ~finally:(fun () -> close_in_noerr ch) (fun () -> loop 1 [])

(** {6 Implementations hidden by module signatures}

    The report resolves a term in the declaration view that typed it. A public
    declaration uses its environment view; a bodyless public declaration falls
    back to its implementation and then follows that implementation's fields.
    This prevents an independent signature proof from replacing a proof
    witness that depends on a relaxed kernel check. *)

type view = Public | Implementation

type vref = view * GlobRef.t

type field_index = {
  constants : constant_body Id.Map.t;
  minds : mutual_inductive_body Id.Map.t;
  modules : module_body Id.Map.t;
}

let empty_field_index = {
  constants = Id.Map.empty;
  minds = Id.Map.empty;
  modules = Id.Map.empty;
}

let index_fields fields =
  let add_mind label mib index =
    let minds = Id.Map.add label mib index.minds in
    let minds = Array.fold_left (fun minds mip ->
        Id.Map.add mip.mind_typename mib minds) minds mib.mind_packets in
    { index with minds }
  in
  List.fold_left (fun index (label, field) -> match field with
      | SFBconst cb -> { index with constants = Id.Map.add label cb index.constants }
      | SFBmind mib -> add_mind label mib index
      | SFBmodule mb -> { index with modules = Id.Map.add label mb index.modules }
      | SFBmodtype _ | SFBrules _ -> index)
    empty_field_index fields

let find_module fields label = Id.Map.find_opt label fields.modules
let find_constant fields label = Id.Map.find_opt label fields.constants
let find_mind fields label = Id.Map.find_opt label fields.minds
type state = {
  env : Environ.env;
  access : Opaqueproof.opaque -> Opaqueproof.opaque_proofterm;
  mutable fields : field_index ModPath.Map.t;
  (* the indexed fields of the implementation of each module looked up so far *)
  mutable public_nodes : node GlobRef.Map.t;
  mutable implementation_nodes : node GlobRef.Map.t;
  (* each object reached so far, keyed by its constant or by the first
     inductive of its block, in the declaration view that typed its use *)
  mutable gen : int;
  keys : Constr.t array;
  gens : int array;
  (* the cache of [seen] *)
}

and node = {
  refs : vref list;
  (* the objects the selected declaration mentions, with the view that
     typed each reference *)
  axiom : bool;
  (* no body: a constant without one, an opaque constant whose body cannot be
     read, or an object neither the environment nor an implementation
     resolves, which is reported rather than left out *)
  flags : (string * string) list;
  (* the relaxed typing conditions the selected object relies on,
     (kind, object) *)
}


let rec fields_of_functor f subs mp0 args = function
  | NoFunctor a -> f subs mp0 args a
  | MoreFunctor (mbid, _, e) ->
    match args with
    | [] -> raise Not_found (* an unapplied functor has no fields *)
    | mpa :: args ->
      let subs =
        Mod_subst.join (Mod_subst.map_mbid mbid mpa (Mod_subst.empty_delta_resolver mpa)) subs in
      fields_of_functor f subs mp0 args e

(* As in vernac/assumptions.ml (#22533): a module whose parent's
   implementation cannot be read is taken from the environment, which holds
   its signature. *)
let rec lookup_module_in_impl st mp = match mp with
  | MPfile _ | MPbound _ -> Environ.lookup_module mp st.env
  | MPdot (mp', lab) ->
    match fields_of_mp st mp' with
    | fields ->
      (match find_module fields lab with
       | Some mb -> mb
       | None -> Environ.lookup_module mp st.env)
    | exception Not_found -> Environ.lookup_module mp st.env

and fields_of_mp st mp =
  match ModPath.Map.find_opt mp st.fields with
  | Some fields -> fields
  | None ->
    let mb = lookup_module_in_impl st mp in
    let raw_fields, inner_mp, subs = fields_of_mb st Mod_subst.empty_subst mp mb [] in
    let fields =
      match mod_expr mb, ModPath.equal inner_mp mp with
      | (Algebraic _, false) ->
        let mp_from = inner_mp in
        let source = lookup_module_in_impl st mp_from in
        let alias = Modops.strengthen_and_subst_module_body mp_from source mp false in
        let fields, inner_mp, subs =
          fields_of_signature Mod_subst.empty_subst mp [] (mod_type alias) in
        let subs =
          if ModPath.equal inner_mp mp then subs
          else Mod_subst.add_mp inner_mp mp (Mod_subst.empty_delta_resolver mp) subs
        in
        Modops.subst_structure subs mp fields
      | _ ->
        let subs =
          if ModPath.equal inner_mp mp then subs
          else if Mod_subst.has_root_delta_resolver mp (mod_delta mb) then
            Mod_subst.add_mp inner_mp mp (Mod_subst.of_body_delta_resolver (mod_delta mb)) subs
          else Mod_subst.add_mp inner_mp mp (Mod_subst.empty_delta_resolver mp) subs
        in
        Modops.subst_structure subs mp raw_fields
    in
    let fields = index_fields fields in
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
  match fields_of_mp st mp with
  | fields -> get fields lab
  | exception Not_found -> None

(* A public term uses its final-environment declaration. When that declaration
   has no body, its proof witness is the implementation. A term already
   reached from an implementation keeps that implementation view. The user
   name, not its canonical target, selects a transparent Include alias. *)
let lookup_constant st view kn =
  let impl () = in_impl st find_constant (Constant.user kn) in
  match view with
  | Public ->
    if Environ.mem_constant kn st.env then
      let cb = Environ.lookup_constant kn st.env in
      if Declareops.constant_has_body cb then Some (Public, cb)
      else match impl () with
        | Some cb -> Some (Implementation, cb)
        | None -> Some (Public, cb)
    else Option.map (fun cb -> (Implementation, cb)) (impl ())
  | Implementation ->
    match impl () with
    | Some cb -> Some (Implementation, cb)
    | None ->
      if Environ.mem_constant kn st.env then Some (Public, Environ.lookup_constant kn st.env)
      else None

let lookup_mind st view mind =
  let impl () = in_impl st find_mind (MutInd.user mind) in
  match view with
  | Public ->
    if Environ.mem_mind mind st.env then Some (Public, Environ.lookup_mind mind st.env)
    else Option.map (fun mib -> (Implementation, mib)) (impl ())
  | Implementation ->
    match impl () with
    | Some mib -> Some (Implementation, mib)
    | None ->
      if Environ.mem_mind mind st.env then Some (Public, Environ.lookup_mind mind st.env)
      else None
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

let empty_refs = GlobRef.Set.empty, GlobRef.Set.empty

let add_ref view obj (public, implementation) = match view with
  | Public -> GlobRef.Set.add obj public, implementation
  | Implementation -> public, GlobRef.Set.add obj implementation

let add_mind view mind refs = add_ref view (GlobRef.IndRef (mind, 0)) refs

(* The primitive type a literal has, which the kernel looks up to type it. *)
let add_prim view prim refs = match prim with
  | Some c -> add_ref view (GlobRef.ConstRef c) refs
  | None -> refs

let refs_to_list (public, implementation) =
  List.map (fun obj -> Public, obj) (GlobRef.Set.elements public)
  @ List.map (fun obj -> Implementation, obj) (GlobRef.Set.elements implementation)

(* The walk keeps its own list of terms to visit, so its depth does not depend
   on the depth of the terms. A term retains the declaration view that typed
   it. The inductive of a [match] and of a projection, and the primitive type
   of a literal or an array, are objects the term relies on even though no
   subterm names them. *)
let rec walk st gen refs = function
  | [] -> refs
  | (view, c) :: todo ->
    let open Constr in
    let retro = Environ.retroknowledge st.env in
    match kind c with
    | Rel _ | Var _ | Sort _ | Meta _ | Evar _ -> walk st gen refs todo
    | Int _ -> walk st gen (add_prim view retro.Retroknowledge.retro_int63 refs) todo
    | Float _ -> walk st gen (add_prim view retro.Retroknowledge.retro_float64 refs) todo
    | String _ -> walk st gen (add_prim view retro.Retroknowledge.retro_string refs) todo
    | Const (kn, _) -> walk st gen (add_ref view (GlobRef.ConstRef kn) refs) todo
    | Ind ((mind, _), _) | Construct (((mind, _), _), _) ->
      walk st gen (add_mind view mind refs) todo
    | Cast _ | Prod _ | Lambda _ | LetIn _ | App _ | Proj _ | Case _ | Fix _ | CoFix _ | Array _ ->
      if seen st gen c then walk st gen refs todo
      else
        let refs = match kind c with
          | Case (ci, _, _, _, _, _, _) -> add_mind view (fst ci.ci_ind) refs
          | Proj (p, _, _) -> add_mind view (Projection.mind p) refs
          | Array _ -> add_prim view retro.Retroknowledge.retro_array refs
          | _ -> refs
        in
        walk st gen refs (fold (fun todo c -> (view, c) :: todo) todo c)

let push_context view ctx todo =
  List.fold_left (fun todo d ->
      Context.Rel.Declaration.fold_constr (fun c todo -> (view, c) :: todo) d todo)
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

let constant_node st view kn =
  match lookup_constant st view kn with
  | None -> unresolved
  | Some (declaration_view, cb) ->
    (* An opaque body that cannot be read is reported as an axiom, as
       vernac/assumptions.ml's [get_constant_body] does. *)
    let body, axiom = match cb.const_body with
      | Def c -> [declaration_view, c], false
      | OpaqueDef o ->
        (match st.access o with
         | c, _ -> [declaration_view, c], false
         | exception e when CErrors.noncritical e -> [], true)
      | Undef _ | Primitive _ | Symbol _ -> [], true
    in
    let refs = walk st (fresh_gen st) empty_refs ((declaration_view, cb.const_type) :: body) in
    { refs = refs_to_list refs; axiom;
      flags = typing_flags (Constant.to_string kn) cb.const_typing_flags [] }

let mind_node st view mind =
  match lookup_mind st view mind with
  | None -> unresolved
  | Some (declaration_view, mib) ->
    let todo =
      Array.fold_left (fun todo mip ->
          push_context declaration_view mip.mind_arity_ctxt
            (Array.fold_left (fun todo c -> (declaration_view, c) :: todo) todo mip.mind_user_lc))
        (push_context declaration_view mib.mind_params_ctxt []) mib.mind_packets
    in
    let refs = walk st (fresh_gen st) empty_refs todo in
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
    { refs = refs_to_list refs; axiom = false; flags }

let node st view obj =
  let nodes = match view with
    | Public -> st.public_nodes
    | Implementation -> st.implementation_nodes
  in
  match GlobRef.Map.find_opt obj nodes with
  | Some n -> n
  | None ->
    let n = match obj with
      | GlobRef.ConstRef kn -> constant_node st view kn
      | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) -> mind_node st view mind
      | GlobRef.VarRef _ -> { refs = []; axiom = false; flags = [] }
    in
    begin match view with
    | Public -> st.public_nodes <- GlobRef.Map.add obj n st.public_nodes
    | Implementation -> st.implementation_nodes <- GlobRef.Map.add obj n st.implementation_nodes
    end;
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
  let rec loop public_seen implementation_seen axioms flags = function
    | [] -> axioms, flags
    | (view, obj) :: todo ->
      let seen = match view with
        | Public -> GlobRef.Set.mem obj public_seen
        | Implementation -> GlobRef.Set.mem obj implementation_seen
      in
      if seen then loop public_seen implementation_seen axioms flags todo
      else
        let n = node st view obj in
        let axioms = if n.axiom then CString.Set.add (name_of obj) axioms else axioms in
        let flags = List.fold_left (fun flags f -> FlagSet.add f flags) flags n.flags in
        let public_seen, implementation_seen = match view with
          | Public -> GlobRef.Set.add obj public_seen, implementation_seen
          | Implementation -> public_seen, GlobRef.Set.add obj implementation_seen
        in
        loop public_seen implementation_seen axioms flags (List.rev_append n.refs todo)
  in
  loop GlobRef.Set.empty GlobRef.Set.empty CString.Set.empty FlagSet.empty [Public, root]

(** {6 The type match} *)

(* The universe comparison that checking [Definition f := model] against a
   monomorphic [Parameter f : <type>] of a sealing module type makes (the
   inference mode of kernel/subtyping.ml's [check_constant]): a comparison that
   does not hold yet adds the constraints it needs, if they are consistent with
   the environment. The state is the universe graph with those constraints; the
   error marks a needed constraint that is inconsistent. *)
let infer_universes : (UGraph.t, unit) Conversion.universe_compare =
  let merge csts g =
    match UGraph.merge_constraints csts g with
    | g -> Result.Ok g
    | exception UGraph.UniverseInconsistency _ -> Result.Error (Some ())
  in
  let leq u v g =
    match UGraph.enforce_leq_alg u v g with
    | _, g -> Result.Ok g
    | exception UGraph.UniverseInconsistency _ -> Result.Error (Some ())
  in
  let same_qualities qcsts = UVars.QPairSet.for_all (fun (q1, q2) -> Sorts.Quality.equal q1 q2) qcsts in
  let compare_sorts pb s1 s2 g =
    let holds = match pb with
      | Conversion.CUMUL -> UGraph.check_leq_sort Sorts.Quality.equal g s1 s2
      | Conversion.CONV -> UGraph.check_eq_sort Sorts.Quality.equal g s1 s2
    in
    if holds then Result.Ok g
    (* As pretyping/reductionops.ml's [Infer]: the qualities must already
       compare, and only the universe constraint is inferred. The checked
       comparison above has decided every case with an impredicative sort. *)
    else match s1, s2 with
      | (Sorts.SProp | Sorts.Prop), _ | _, (Sorts.SProp | Sorts.Prop) -> Result.Error None
      | _ when not (Sorts.Quality.equal (Sorts.quality s1) (Sorts.quality s2)) -> Result.Error None
      | _ ->
        let u1 = Sorts.univ_of_sort s1 and u2 = Sorts.univ_of_sort s2 in
        match pb with
        | Conversion.CUMUL -> leq u1 u2 g
        | Conversion.CONV ->
          (* As engine/univSubst.ml's [enforce_eq]: only two levels can be made equal. *)
          match Univ.Universe.level u1, Univ.Universe.level u2 with
          | Some _, Some _ -> Result.bind (leq u1 u2 g) (leq u2 u1)
          | _ -> Result.Error (Some ())
  in
  let compare_instances ~flex u1 u2 g =
    if UGraph.check_eq_instances Sorts.Quality.equal g u1 u2 then Result.Ok g
    else if flex then Result.Error None
    else
      let qcsts, ucsts =
        UVars.enforce_eq_instances u1 u2 (UVars.QPairSet.empty, Univ.UnivConstraints.empty) in
      if same_qualities qcsts then merge ucsts g else Result.Error None
  in
  let compare_cumul_instances pb variances u1 u2 g =
    let qcsts, ucsts = Conversion.get_cumulativity_constraints pb variances u1 u2 in
    if same_qualities qcsts then merge ucsts g else Result.Error None
  in
  { Conversion.compare_sorts; compare_instances; compare_cumul_instances }

(* Whether the model constant can stand for the trusted constant in a module
   sealed by a signature that declares the trusted type T: whether [Definition
   f := model] ([Polymorphic] when T is) is accepted for the field [Parameter f
   : T] (kernel/subtyping.ml's [check_constant]). The model's type must be
   cumulative to T. Against a monomorphic T, a needed universe constraint is
   added when it is consistent with the environment; against a polymorphic T,
   the definition's universe context must be T's and adds no constraint.
   Elaborating the definition takes a polymorphic model at fresh universes,
   and can minimize them when the model's universe context has sort variables
   or constraints; this check does not replay that, so it answers
   [universes-differ] for such a model, which the sealing may still accept. *)
let type_verdict env model trusted =
  let cm = Environ.lookup_constant model env and ct = Environ.lookup_constant trusted env in
  let infer env =
    let state = Environ.universes env, infer_universes in
    match Conversion.generic_conv Conversion.CUMUL ~l2r:false TransparentState.full env state
            cm.const_type ct.const_type with
    | Result.Ok _ -> "match"
    | Result.Error None -> "mismatch"
    | Result.Error (Some ()) -> "universes-differ"
  in
  (* The definition's context [am] must be T's context [at]; the types are
     compared under [at]. A failure that ignoring universe levels removes needs a
     constraint that [at] does not give. *)
  let against_polymorphic am at =
    if Subtyping.check_polymorphic_universes env at am then
      let env = Environ.push_context ~strict:false (UVars.AbstractContext.repr at) env in
      match Conversion.default_conv_leq env cm.const_type ct.const_type with
      | Result.Ok () -> "match"
      | Result.Error () ->
        match Conversion.default_conv_leq (Environ.set_type_in_type true env)
                cm.const_type ct.const_type with
        | Result.Ok () -> "universes-differ"
        | Result.Error () -> "mismatch"
    else "universes-differ"
  in
  let minimizable am =
    fst (UVars.AbstractContext.size am) > 0
    || not (PConstraints.is_empty (UVars.UContext.constraints (UVars.AbstractContext.repr am)))
  in
  match cm.const_universes, ct.const_universes with
  | Monomorphic, Monomorphic -> infer env
  | Monomorphic, Polymorphic at -> against_polymorphic UVars.AbstractContext.empty at
  | Polymorphic am, _ when minimizable am -> "universes-differ"
  | Polymorphic am, Monomorphic ->
    (* The model's bound universes are fresh in [env]: they are its instance. *)
    infer (Environ.push_context ~strict:false (UVars.AbstractContext.repr am) env)
  | Polymorphic am, Polymorphic at -> against_polymorphic am at

(** {6 The report} *)

(* One message per line, so that a long report never builds one [Pp.t]. *)
let line fmt = Printf.ksprintf (fun s -> Feedback.msg_notice (Pp.str s)) fmt

(* Test-only seam: a test sets this for one process to exercise the public
   incomplete-report contract. It has no effect unless the test variable is
   explicitly set. *)
let test_fault () =
  match Sys.getenv_opt "COQ_TEST_SUITE_STATEMENT_REPORT_FAILURE" with
  | Some "1" -> CErrors.user_err Pp.(str "test statement-report failure")
  | None | Some _ -> ()

let print env access requests =
  let index =
    Environ.fold_constants (fun c _ acc -> CString.Map.add (Constant.to_string c) c acc)
      env CString.Map.empty
  in
  let st = {
    env; access; fields = ModPath.Map.empty;
    public_nodes = GlobRef.Map.empty; implementation_nodes = GlobRef.Map.empty; gen = 0;
    keys = Array.make cache_size Constr.mkProp; gens = Array.make cache_size (-1);
  } in
  line "STATEMENT REPORT";
  test_fault ();
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
