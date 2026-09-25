(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*s Production of Scala (Scala 3) syntax. *)

(* Local (non-top-level) positions are printed with static type [Any],
   so every application through them goes through a cast-then-call
   [(f.asInstanceOf[Any => Any])(arg)]. Top-level [Dfix]/[Dterm]
   declarations get a real, precise Scala signature instead (see
   [typed_signature]), and the rest of this file removes as many of the
   casts above as remain provably safe once a real type is available
   ([known_type], [already_satisfies], [apply_one_step],
   [pp_apply_typed]). *)

open Pp
open CErrors
open Util
open Names
open Table
open Miniml
open Mlutil
open Common

(*s Scala renaming issues. *)

let keywords =
  List.fold_right (fun s -> Id.Set.add (Id.of_string s))
    [ (* Scala 3 hard keywords *)
      "abstract"; "case"; "catch"; "class"; "def"; "do"; "else"; "enum";
      "export"; "extends"; "false"; "final"; "finally"; "for"; "given";
      "if"; "implicit"; "import"; "lazy"; "match"; "new"; "null"; "object";
      "override"; "package"; "private"; "protected"; "return"; "sealed";
      "super"; "then"; "this"; "throw"; "trait"; "true"; "try"; "type";
      "val"; "var"; "while"; "with"; "yield";
      (* Scala 3 soft keywords / contextual identifiers, avoided for safety.
         Note: "macro" was a Scala 2-only soft keyword (`def foo = macro
         impl`), dropped along with the old macro system; it is a plain
         identifier in Scala 3 and deliberately not listed here. *)
      "derives"; "end"; "extension"; "infix"; "inline"; "opaque"; "open";
      "transparent"; "using";
      (* Members inherited from Any / AnyRef that are best not shadowed
         at top level *)
      "equals"; "hashCode"; "toString"; "getClass"; "wait"; "notify";
      "notifyAll"; "synchronized"; "clone"; "asInstanceOf"; "isInstanceOf";
      (* Our own helpers and the usual extraction dummy identifiers *)
      "unsafeCoerce"; "unit"; "Unit"; "Any"; "Nothing"; "Null";
      "_"; "__" ]
    Id.Set.empty

(* Note: do not shorten [str "foo" ++ fnl ()] into [str "foo\n"],
   the '\n' character interacts badly with the Format boxing mechanism *)

let pp_comment s = str "// " ++ hov 0 s ++ fnl ()
let pp_bracket_comment s = str "/* " ++ hov 0 s ++ str " */"

(* Unlike OCaml, Scala identifiers cannot contain an apostrophe, which is
   nonetheless a very common character in Rocq-chosen names (e.g. [n'],
   [IHn']). We turn it into an underscore whenever we print an actual
   local identifier (as opposed to a global reference, which already goes
   through [Common.unquote], or a name only used inside a comment). *)
let pr_id id = str (String.map (fun c -> if c == '\'' then '_' else c) (Id.to_string id))

(* Every extracted file's contents are wrapped in a single [object]
   named after the module (see [preamble]): [mod_name] cleaned up the
   same way [pr_id] does, capitalized to follow Scala's own naming
   convention for an [object] - purely cosmetic, unlike the apostrophe
   cleanup, since Scala does not actually require it. *)
let pr_object_name mod_name =
  str (String.capitalize_ascii
         (String.map (fun c -> if c == '\'' then '_' else c) (Id.to_string mod_name)))

let pp_header_comment = function
  | None -> mt ()
  | Some com -> pp_bracket_comment com ++ fnl2 ()

(* [package foo.bar], from [Set Extraction Scala Package "foo.bar".]
   (empty - the default - prints nothing). Must come before the
   wrapping [object] (see [preamble]): a Scala [package] clause is a
   file-level statement, not something that can itself live inside an
   object. *)
let pp_package_header () =
  let pkg = scala_package () in
  if String.is_empty pkg then mt ()
  else str "package " ++ str pkg ++ fnl2 ()

(*s No modular extraction. *)

(* Two whole-structure analyses computed once by [pp_struct]
   ([register_structure]) and read from everywhere else while that same
   structure is being printed: [cons_fields] gives a constructor's
   declared field types (its inductive's [ip_types]), keyed by the
   constructor's own global reference together with its inductive's
   arity; [glob_types] gives a top-level [Dfix]/[Dterm]'s declared type,
   keyed by its global reference; [needs_lazy] says whether the
   structure has any coinductive type, which decides whether [RocqLazy]
   gets emitted (see [preamble]).

   Held in one [ref] rather than passed as an argument because
   [pp_decl] can be called on its own, once [pp_struct] has already
   populated it (isolated single-declaration printing in
   [extract_env.ml]) - [pp_decl]'s signature is shared by every backend,
   so it cannot carry this backend-specific extra state. Reset on every
   [pp_struct] call, so it never leaks across unrelated extraction
   commands. *)
type struct_info = {
  cons_fields : (int * ml_type list) Refmap'.t;
  glob_types : ml_type Refmap'.t;
  needs_lazy : bool;
}

let empty_struct_info =
  { cons_fields = Refmap'.empty; glob_types = Refmap'.empty; needs_lazy = false }

let struct_info = ref empty_struct_info

let find_cons_fields r = Refmap'.find_opt r (!struct_info).cons_fields
let find_glob_type r = Refmap'.find_opt r (!struct_info).glob_types

let register_ind_packet acc p =
  if p.ip_logical then acc
  else
    let nparams = List.length p.ip_vars in
    let n = Array.length p.ip_consnames_ref in
    let rec loop acc j =
      if j >= n then acc
      else loop (Refmap'.add p.ip_consnames_ref.(j) (nparams, p.ip_types.(j)) acc) (j+1)
    in
    loop acc 0

let rec register_structure_elem info (_,se) = match se with
  | SEdecl (Dind ind) ->
    { info with
      cons_fields = Array.fold_left register_ind_packet info.cons_fields ind.ind_packets;
      needs_lazy = info.needs_lazy || ind.ind_kind == Coinductive }
  | SEdecl (Dtype _) -> info
  | SEdecl (Dterm (r,_,t)) -> { info with glob_types = Refmap'.add r t info.glob_types }
  | SEdecl (Dfix (rv,_,typs)) ->
    let glob_types =
      List.fold_left2 (fun acc r t -> Refmap'.add r t acc)
        info.glob_types (Array.to_list rv) (Array.to_list typs)
    in
    { info with glob_types }
  | SEmodule m -> register_module_expr info m.ml_mod_expr
  | SEmodtype _ -> info

and register_module_expr info = function
  | MEstruct (_,sel) -> List.fold_left register_structure_elem info sel
  | MEfunctor _ | MEident _ | MEapply _ -> info

let register_structure (s : ml_structure) =
  List.fold_left
    (fun info (_,sel) -> List.fold_left register_structure_elem info sel)
    empty_struct_info s

(* [Lazy.t]/[lazy]/[Lazy.force] reimplemented on Scala's native
   laziness: a by-name parameter [=> T] is a thunk, a [lazy val] caches
   it on first access. Not a one-liner [case class] because Scala
   forbids by-name parameters there. *)
let pp_lazy_class =
  str "final class RocqLazy[T](thunk: => T) {" ++ fnl () ++
  str "  lazy val force: T = thunk" ++ fnl () ++
  str "}" ++ fnl () ++
  str "object RocqLazy {" ++ fnl () ++
  str "  def apply[T](thunk: => T): RocqLazy[T] = new RocqLazy(thunk)" ++ fnl () ++
  str "}"

(* Every extracted file is a package declaration (optional, see
   [pp_package_header]) followed by one [object mod_name { ... }]
   wrapping everything else - the dummy value, [RocqLazy] (both below)
   and the whole structure printed by [pp_struct], which closes the
   brace this opens. Doing this unconditionally, not just when a
   package is set, keeps two separately-extracted files from each
   defining their own top-level [RocqLazy]/[Nat]/... and colliding as
   soon as both are compiled together, package or not. *)
let preamble _table mod_name comment _used_modules usf =
  pp_header_comment comment ++
  pp_package_header () ++
  str "object " ++ pr_object_name mod_name ++ str " {" ++ fnl2 () ++
  (if not usf.mldummy then mt ()
   else str "val __ : Any = ()" ++ fnl2 ())
  ++
  (if not (!struct_info).needs_lazy then mt ()
   else pp_lazy_class ++ fnl2 ())

(*s The pretty-printer for Scala syntax *)

let pp_global table k r =
  if is_inline_custom r then str (find_custom r) else str (Common.pp_global table k r)

let pp_global_with_key table k key r =
  if is_inline_custom r then str (find_custom r)
  else str (Common.pp_global_with_key table k key r)

(*s Record field names, computed the same way OCaml's backend does
    ([get_record_fields]/[get_ind]/[kn_of_ind]): an explicitly-given
    field is named after its projection constant, an anonymous one
    falls back to a synthetic [Type__i]. *)

let get_ind r = let open GlobRef in match r.glob with
  | IndRef _ -> r
  | ConstructRef (ind,_) -> { glob = IndRef ind; inst = r.inst }
  | _ -> assert false

let kn_of_ind r = let open GlobRef in match r.glob with
  | IndRef (kn,_) -> MutInd.user kn
  | _ -> assert false

let pp_one_field table r i = function
  | Some r' -> pp_global_with_key table Term (kn_of_ind (get_ind r)) r'
  | None -> pp_global table Type (get_ind r) ++ str "__" ++ int i

let pp_fields table r fields = List.mapi (pp_one_field table r) fields

let pp_field table r fields i = pp_one_field table r i (List.nth fields i)

(*s Pretty-printing of types. [par] is a boolean indicating whether
    parentheses are needed or not. Type variables are printed as-is
    (Scala does not require capitalised type parameter names). *)

let pp_type_params = function
  | [] -> mt ()
  | l -> str "[" ++ prlist_with_sep (fun () -> str ", ") pr_id l ++ str "]"

let rec pp_type table par vl t =
  let rec pp_rec par = function
    | Tmeta _ | Tvar' _ -> assert false
    | Tvar i ->
      (try pr_id (List.nth vl (pred i))
       with Failure _ -> str "T" ++ int i)
    | Tglob (r,[]) -> pp_global table Type r
    | Tglob (gr,l)
        when not (keep_singleton ()) && Rocqlib.check_ref sig_type_name gr.glob ->
          pp_type table false vl (List.hd l)
    | Tglob (r,l) ->
        pp_global table Type r ++ str "[" ++
        prlist_with_sep (fun () -> str ", ") (pp_type table false vl) l ++ str "]"
    | Tarr (t1,t2) ->
        pp_par par (pp_rec true t1 ++ str " => " ++ pp_rec false t2)
    | Tdummy _ -> str "Unit"
    | Tunknown -> str "Any"
    | Taxiom -> str "Any" ++ spc () ++ pp_bracket_comment (str "AXIOM TO BE REALIZED")
  in
  hov 0 (pp_rec par t)

(* [extraction.ml] marks a function's own generalized type variables as
   [Tvar'], not [Tvar], inside the body it extracts ([Mlutil.var2var']);
   [pp_type] flatly refuses to print [Tvar'] ([assert false]). Converts
   a scrutinee type sourced value back to [Tvar] before it can reach
   [tenv] or a cast target. *)
let rec devar' = function
  | Tvar' i -> Tvar i
  | Tmeta {contents = Some t} -> devar' t
  | Tarr (a,b) -> Tarr (devar' a, devar' b)
  | Tglob (r,l) -> Tglob (r, List.map devar' l)
  | a -> a

(* The real, concrete type of a [Pusual r] branch's bound fields, given
   the [MLcase]'s own scrutinee type [typ]. [None] (fall back to [Any])
   unless [typ] is a [Tglob] of exactly [r]'s inductive's own arity. *)
let pattern_field_types typ r =
  match find_cons_fields r, typ with
  | Some (nparams, fts), Tglob (_, args) when Int.equal (List.length args) nparams ->
    let args = List.map devar' args in
    Some (List.map (type_subst_list args) fts)
  | _ -> None

(* The [tenv] extension one [MLcase] branch pushes for its bound [ids],
   given the scrutinee's known type [typ] and the branch's pattern [p] -
   shared between [pp_one_pat] and [known_type]'s own [MLcase] case. *)
let branch_tenv_ext typ p ids =
  match p with
  | Pusual r ->
    (match pattern_field_types typ r with
     | Some fts when Int.equal (List.length fts) (List.length ids) ->
       List.rev_map (fun ft -> Some ft) fts
     | _ -> List.map (fun _ -> None) ids)
  | Pcons _ | Ptuple _ | Pwild | Prel _ -> List.map (fun _ -> None) ids

(*s Pretty-printing of expressions. Function application is always
    printed as a chain of curried, parenthesised calls
    [f(arg1)(arg2)...], matching the way every function value (whether
    top-level or local) is compiled as a chain of one-argument Scala
    functions. *)

(* The typing context, threaded as one value everywhere [table]/[env]/
   [tenv]/[self] used to be four separate parameters repeated at every
   call site: [table] (global naming state), [env] (de Bruijn naming),
   [tenv] (each in-scope variable's statically known type, kept in
   lockstep with [env]) and [self] (the enclosing top-level
   [Dfix]/[Dterm]'s own type parameters, once [typed_signature] has
   named them; [None] outside any typed body). Updated only at the
   handful of places that push a variable, extend [tenv], or fix [self]
   ([ctx_push_vars], [ctx_ext_tenv], and a plain [{ ctx with self =
   ... }]); left unchanged by everything nested inside. *)
type ctx = {
  table : State.t;
  env : Common.env;
  tenv : ml_type option list;
  self : (global option * Id.t list) option;
}

let init_ctx table = { table; env = empty_env table (); tenv = []; self = None }

let ctx_push_vars ids ctx =
  let ids', env = push_vars ids ctx.env in
  ids', { ctx with env }

let ctx_ext_tenv extra ctx = { ctx with tenv = extra @ ctx.tenv }

(* [t] with every one of its own type variables instantiated to [Any] -
   always a well-formed cast target (a no-op substitution if [t] is
   itself a bare type variable). Only right when [t]'s variables are
   *not* some enclosing definition's own, nameable type parameters - see
   [pp_cast_target] below for that case. *)
let pp_any_instantiated_type ctx t =
  let vl = List.init (type_maxvar t) (fun _ -> Id.of_string "Any") in
  pp_type ctx.table false vl t

(* Mirrors [get_db_name]: the statically known type of de Bruijn
   variable [n], if any. *)
let get_db_type n (tenv : ml_type option list) = List.nth tenv (pred n)

(* Same equality [Mlutil.eq_ml_type] uses for a [Tglob] head, but not
   exported from there: two type-level references name the very same
   inductive/type declaration. *)
let eq_glob_head r1 r2 = GlobRef.CanOrd.equal r1.glob r2.glob

(* Every type variable occurring anywhere in [t]. *)
let rec tvars_of = function
  | Tvar i | Tvar' i -> Int.Set.singleton i
  | Tarr (t1,t2) -> Int.Set.union (tvars_of t1) (tvars_of t2)
  | Tglob (_,l) -> List.fold_left (fun s t -> Int.Set.union s (tvars_of t)) Int.Set.empty l
  | Tmeta _ | Tdummy _ | Tunknown | Taxiom -> Int.Set.empty

(* Whether [f] is a reference to the *recursive* definition [ctx.self]
   identifies (through passthrough [MLmagic]s). *)
let rec is_self_call self = function
  | MLmagic a -> is_self_call self a
  | MLglob r -> (match self with Some (Some sr,_) -> eq_glob_head sr r | _ -> false)
  | _ -> false

(* Broader than [is_self_call]: also true of a bare variable reference
   ([MLrel]) - calling an already-typed local value is, for Scala, not
   generic method invocation either, so its [Tvar]s are just as fixed as
   [self]'s own. See [apply_one_step]. *)
let is_self_relative_call self = function
  | MLrel _ -> true
  | f -> is_self_call self f

(* A cast target for [t], whose own type variables might be the
   *current* definition's real, already-fixed type parameters rather
   than free ones ([self_relative] - see [apply_one_step]): prints using
   [ctx.self]'s own real names when that's the case (blanket [Any] would
   be actively wrong there, not just imprecise - invariant generics),
   falls back to [pp_any_instantiated_type] otherwise. *)
let pp_cast_target ctx self_relative t =
  match ctx.self with
  | Some (_, vl) when self_relative ->
    let extra = max 0 (type_maxvar t - List.length vl) in
    let vl = vl @ List.init extra (fun _ -> Id.of_string "Any") in
    pp_type ctx.table false vl t
  | _ -> pp_any_instantiated_type ctx t

(* The cast target for a coinductive scrutinee's [RocqLazy] wrapper, when
   [already_satisfies] can't prove the scrutinee already has type [typ].
   [pp_cast_target]'s [self_relative] gating is unconditionally true
   here ([typ] is always phrased relative to the current definition's
   own generalization). Only ever instantiates *individual* unresolved
   type arguments to [Any], never the whole type: that is what keeps a
   coinductive match's bound fields safe to type precisely, since the
   type parameters left untouched still carry their real identity. *)
let pp_coinductive_force_target ctx typ =
  match typ with
  | Tglob (r, args) ->
    let args = List.map devar' args in
    str "RocqLazy[__" ++ pp_global ctx.table Type r ++
    (match args with
     | [] -> mt ()
     | _ ->
       str "[" ++
       prlist_with_sep (fun () -> str ", ") (pp_cast_target ctx true) args ++
       str "]")
    ++ str "]"
  | _ -> str "RocqLazy[Any]"

(* The state threaded through one curried application by
   [apply_one_step]/[resolve_apply_type]/[pp_apply_typed]: the callee's
   remaining type, and the two sets of type variables pinned so far -
   [pinned_real] to a type an argument already provably has,
   [pinned_any] to [Any] by a previous step's cast. Named fields, not a
   plain tuple: [pinned_real] and [pinned_any] are both [Int.Set.t], and
   a positional mix-up between them would still type-check while
   silently choosing the wrong casts. *)
type apply_state = {
  ty : ml_type option;
  pinned_real : Int.Set.t;
  pinned_any : Int.Set.t;
}

(* The statically known type of an already-built expression, using the
   same "known positions" as [tenv]/[glob_types] plus [MLapp]
   ([resolve_apply_type]) and an [MLcase] whose branches all agree
   ([Mlutil.eq_ml_type], full equality - we need to *name* one type, not
   just prove a shape match). [None] (treated as [Any]) everywhere else -
   a fresh lambda literal is never looked through. *)
let rec known_type ctx = function
  | MLrel n -> get_db_type n ctx.tenv
  | MLglob r -> find_glob_type r
  | MLmagic a -> known_type ctx a
  | MLapp (f, args) ->
    (match known_type ctx f with
     | None -> None
     | Some ty -> resolve_apply_type ctx (is_self_relative_call ctx.self f) ty args)
  | MLcase (typ, _, pv) ->
    let pat_typ =
      if is_coinductive_type (State.get_table ctx.table) typ then Tunknown else typ
    in
    let branch_type (ids, p, tail) =
      known_type (ctx_ext_tenv (branch_tenv_ext pat_typ p ids) ctx) tail
    in
    let tys = Array.to_list (Array.map branch_type pv) in
    (match tys with
     | Some ty0 :: rest when List.for_all (function
         | Some ty -> eq_ml_type ty ty0
         | None -> false) rest -> Some ty0
     | _ -> None)
  | MLcons (_, r, _) as c
    when not (is_native_char c) && not (is_native_string c) && not (is_inline_custom r) ->
    (* The constructor's own inductive type, own type parameters left
       unspecified ([already_satisfies]'s [Tglob] case only compares
       heads). Excluded: a native char/string literal or inline-custom
       constructor prints as something else entirely, not a value of
       the inductive's own case-class hierarchy. *)
    Some (Tglob (get_ind r, []))
  | _ -> None

(* Whether argument [a] already provably has parameter type [t1],
   deliberately loose about what's inside [t1] where it can afford to be
   (a shared [Tarr]/[Tarr] or [Tglob] head is enough - Scala's own
   inference unifies the rest structurally). A bare type variable is
   where looseness runs out: [Tvar i] is only satisfied by an [a]
   independently known to carry that exact index. *)
and already_satisfies ctx a t1 = match t1, known_type ctx a with
  | Tarr _, Some (Tarr _) -> true
  | Tglob (r1,_), Some (Tglob (r2,_)) -> eq_glob_head r1 r2
  | (Tvar i | Tvar' i), Some (Tvar j | Tvar' j) -> Int.equal i j
  | _ -> false

(* One step of a curried application: given the callee's remaining type
   and the [pinned_real]/[pinned_any] sets accumulated so far, decides
   whether [arg] applies directly ([`Direct (Some t)] with a cast, or
   [`Direct None] without), or the rest of the call falls back to the
   uniform [Any => Any] scheme ([`Fallback]). A pure verdict, with no
   [Pp.t] involved, so [pp_apply_typed] (which prints it) and
   [resolve_apply_type] (which only needs the state transition) can
   never disagree. [self_relative] bypasses the pinned-variable
   tracking entirely and makes a bare [Tvar] parameter *not*
   automatically safe the way [Tunknown] still is: the current
   definition's own type parameters are already fixed, real types, not
   free ones a cast to [Any] could safely stand in for. *)
and apply_one_step ctx self_relative st arg =
  match st.ty with
  | Some (Tarr (t1,t2))
    when self_relative || Int.Set.is_empty (Int.Set.inter st.pinned_real (tvars_of t1)) ->
    let safely_any = match t1 with
      | Tunknown | Tmeta _ -> true
      | Tvar _ | Tvar' _ -> not self_relative
      | Tglob _ | Tarr _ | Tdummy _ | Taxiom -> false
    in
    if safely_any then
      `Direct None, { st with ty = Some t2 }
    else if (self_relative || Int.Set.is_empty (Int.Set.inter st.pinned_any (tvars_of t1)))
            && already_satisfies ctx arg t1 then
      `Direct None, { st with ty = Some t2; pinned_real = Int.Set.union st.pinned_real (tvars_of t1) }
    else
      `Direct (Some t1), { st with ty = Some t2; pinned_any = Int.Set.union st.pinned_any (tvars_of t1) }
  | _ -> `Fallback, { st with ty = None }

(* The type a whole (possibly partial) application [ty] applied to
   [args] would end up with if printed by [pp_apply_typed] - folds
   [apply_one_step] over [args], [None] as soon as any step falls back. *)
and resolve_apply_type ctx self_relative ty args =
  let final =
    List.fold_left
      (fun st arg -> snd (apply_one_step ctx self_relative st arg))
      { ty = Some ty; pinned_real = Int.Set.empty; pinned_any = Int.Set.empty } args
  in
  final.ty

(* Sibling fields of one constructor call can share an inductive type
   parameter (e.g. [Scons : A -> stream A -> stream A] has [A] in both
   fields): when a field's raw type is a bare [Tvar]/[Tvar'] and that
   argument's real, fully ground type is known, that pins down the
   parameter for every other field mentioning it, instead of
   instantiating to [Any]. Returns one [ml_type] per inductive type
   parameter ([Tunknown] wherever nothing was discovered), plus
   [unsafe]: type parameters that must never be trusted this way
   because a bare-[Tvar] field with no [known_type] can be a
   coinductive-match skolem rather than a genuine free [Any].
   [fts]/[args] are a constructor's declared field types and its actual
   arguments, always the same length. *)
let discover_field_instantiation ctx nparams fts args =
  let paired = List.combine fts args in
  let unsafe =
    List.fold_left
      (fun acc (ft, arg) -> match ft with
         | (Tvar i | Tvar' i) when Option.is_empty (known_type ctx arg) -> Int.Set.add i acc
         | _ -> acc)
      Int.Set.empty paired
  in
  (* Only a fully ground discovered type is safe to print here: a
     sibling argument can be known only up to some *other* enclosing
     definition's own type variable, which isn't printable without that
     definition's naming environment. [Tunknown] (prints as [Any]) is
     always safe short of that. *)
  let found = Array.make nparams Tunknown in
  List.iter
    (fun (ft, arg) -> match ft with
       | (Tvar i | Tvar' i) when i >= 1 && i <= nparams && not (Int.Set.mem i unsafe) ->
         (match known_type ctx arg with
          | Some ty when Int.Set.is_empty (tvars_of ty) -> found.(i - 1) <- ty
          | _ -> ())
       | _ -> ())
    paired;
  (Array.to_list found, unsafe)

(* The per-field cast verdict [MLcons] needs: whether one field's raw
   declared type [ft], with the sibling-discovered instantiation
   [inst]/[unsafe] from [discover_field_instantiation] not yet applied,
   needs a cast before its own field position, and if so, to what. *)
type field_cast =
  | FieldNoCast
  | FieldCastAny of ml_type
  | FieldCastTo of ml_type

let field_cast_decision ctx unsafe inst ft arg =
  match ft with
  (* Would cast to [Any] anyway once instantiated: skip. *)
  | Tvar _ | Tvar' _ | Tmeta _ | Tunknown -> FieldNoCast
  | ft when not (Int.Set.is_empty (Int.Set.inter (tvars_of ft) unsafe)) ->
    (* Not safe to resolve via a sibling field here: fall back to
       instantiating this field's own variables to [Any]. *)
    FieldCastAny ft
  | ft ->
    let ft = type_subst_list inst ft in
    if already_satisfies ctx arg ft then FieldNoCast else FieldCastTo ft

(* Prints an application of [hd] (statically known type [ty], if any) to
   [args], folding [apply_one_step] and turning each step's verdict into
   printed Scala. *)
let pp_apply_typed ctx hd ty self_relative par args = match args with
  | [] -> hd
  | _  ->
    let doc, _ =
      List.fold_left
        (fun (acc,st) (a,pp_a) ->
           match apply_one_step ctx self_relative st a with
           | `Direct None, st' -> (acc ++ str "(" ++ pp_a ++ str ")"), st'
           | `Direct (Some t1), st' ->
             let pp_a = str "(" ++ pp_a ++ str ").asInstanceOf[" ++
                        pp_cast_target ctx self_relative t1 ++ str "]"
             in
             (acc ++ str "(" ++ pp_a ++ str ")"), st'
           | `Fallback, st' ->
             (str "(" ++ acc ++ str ".asInstanceOf[Any => Any])(" ++ pp_a ++ str ")"), st')
        (hd, { ty; pinned_real = Int.Set.empty; pinned_any = Int.Set.empty }) args
    in
    pp_par par doc

let pp_apply ctx st par args = pp_apply_typed ctx st None false par args

let pp_apply2 ctx st par args = match args with
  | [] -> pp_par par st
  | _  -> pp_apply ctx st par args

let pp_abst = function
  | [] -> mt ()
  | l ->
    prlist_with_sep (fun () -> mt ())
      (fun id -> str "(" ++ pr_id id ++ str ": Any) => ") l

(* Same as [pp_abst], but with each parameter's real domain type (see
   [typed_signature]) instead of [Any]. *)
let pp_abst_typed ctx vl = function
  | [] -> mt ()
  | l ->
    prlist_with_sep (fun () -> mt ())
      (fun (id,t) -> str "(" ++ pr_id id ++ str ": " ++ pp_type ctx.table false vl t ++ str ") => ")
      l

(* Forces a fresh line at a small, fixed indent right after a leading
   parameter chain, whenever there was at least one parameter - without
   this, the body (typically a [match]) starts wherever the last
   parameter happened to leave off, and every [case] aligns under that
   arbitrarily deep column. *)
let pp_body_after_params bl body =
  if List.is_empty bl then body else fnl () ++ str "  " ++ body

(* Uniform arity type [Any => ... => Any] ([n] arrows), used to ascribe
   a recursive definition that has no better, real type available
   (Scala requires an explicit result type for recursive [def]s). *)
let pp_any_chain n =
  prlist_with_sep (fun () -> str " => ") (fun () -> str "Any") (List.init (n+1) (fun _ -> ()))

(* Decomposes a [Dfix]/[Dterm]'s stored, fully-generalized type [typ]
   into fresh Scala type-parameter names [vl], the real domain type of
   each of the [n] printed parameters, and [rest] (whatever's left of
   the type after those [n] parameters). [None] - fall back to the
   uniform [Any] scheme - when [typ] is degenerate or has fewer arrows
   than [n]. *)
let typed_signature typ n =
  match typ with
  | Taxiom | Tunknown -> None
  | _ ->
    let domains, codomain = type_decomp typ in
    if n > List.length domains then None
    else
      let doms, rest_doms = List.chop n domains in
      let maxvar = type_maxvar typ in
      let vl = rename_tvars keywords
          (List.init maxvar (fun i -> Id.of_string ("T" ^ string_of_int (i+1))))
      in
      Some (vl, doms, type_recomp (rest_doms, codomain))

let expr_needs_par = function
  | MLlam _  -> true
  | MLcase _ -> false (* printed as a self-contained [... match { ... }] block *)
  | _        -> false

(* The pure shape decision behind [pp_record_proj]: [None] wherever the
   match cannot be printed as a field projection (mirrors OCaml's own
   [pp_record_proj]), [Some] the resolved field together with the
   branch's own [ids]/pattern/extra-argument list - no shape decision
   left once this returns, only printing. *)
let record_proj_shape ctx typ pv =
  let fields = record_fields_of_type (State.get_table ctx.table) typ in
  if List.is_empty fields then None
  else if not (Int.equal (Array.length pv) 1) then None
  else if has_deep_pattern pv then None
  else
    let (ids,pat,body) = pv.(0) in
    let n = List.length ids in
    let no_patvar a = not (List.exists (ast_occurs_itvl 1 n) a) in
    match
      (match body with
       | MLrel i | MLmagic (MLrel i) when i <= n -> Some (i, [])
       | MLapp (MLrel i, a) | MLmagic (MLapp (MLrel i, a))
       | MLapp (MLmagic (MLrel i), a) when i <= n && no_patvar a -> Some (i, a)
       | _ -> None)
    with
    | None -> None
    | Some (rel_i, a) ->
      let rec lookup_rel i idx = function
        | Prel j :: l -> if Int.equal i j then Some idx else lookup_rel i (idx+1) l
        | Pwild :: l -> lookup_rel i (idx+1) l
        | _ -> None
      in
      let r_idx = match pat with
        | Pusual r -> Some (r, n - rel_i)
        | Pcons (r,l) -> (match lookup_rel rel_i 0 l with
            | Some idx -> Some (r, idx)
            | None -> None)
        | _ -> None
      in
      (* A custom-extracted constructor isn't printed as a case class. *)
      (match r_idx with
       | Some (r, idx) when not (is_inline_custom r) -> Some (fields, ids, pat, r, idx, a)
       | _ -> None)

let rec pp_expr ctx par args = function
  | MLrel n -> pp_expr_rel ctx par args n
  | MLapp (f,args') ->
      let stl = List.map (fun a -> (a, pp_expr ctx true [] a)) args' in
      pp_expr ctx par (stl @ args) f
  | MLlam _ as a -> pp_expr_lam ctx par args a
  | MLletin (id,a1,a2) -> pp_expr_letin ctx par args id a1 a2
  | MLglob r -> pp_expr_glob ctx par args r
  | MLcons (_,r,a) as c ->
      assert (List.is_empty args);
      pp_expr_cons ctx c r a
  | MLtuple l ->
      assert (List.is_empty args);
      str "(" ++ prlist_with_sep (fun () -> str ", ") (pp_expr ctx false []) l ++ str ")"
  | MLcase (_,t,pv) when is_custom_match pv -> pp_expr_custom_match ctx par args t pv
  | MLcase (typ,t,pv) -> pp_expr_case ctx par args typ t pv
  | MLfix (i,ids,defs) ->
      let ids',ctx' = ctx_push_vars (List.rev (Array.to_list ids)) ctx in
      let ctx' = ctx_ext_tenv (List.map (fun _ -> None) ids') ctx' in
      pp_fix ctx' par i (Array.of_list (List.rev ids'),defs) args
  | MLexn s ->
      (* An [MLexn] may be applied, but I don't really care. *)
      pp_par par (str "throw new RuntimeException(" ++ qs s ++ str ")")
  | MLdummy k ->
      (* An [MLdummy] may be applied, but I don't really care. *)
      (match msg_of_implicit k with
       | "" -> pp_apply_typed ctx (str "__") None false par args
       | s -> pp_apply_typed ctx (str "__") None false par args ++ spc () ++ pp_bracket_comment (str s))
  | MLmagic a ->
      (* A no-op in our [Any]-erased encoding: print straight through. *)
      pp_expr ctx par args a
  | MLaxiom s -> pp_par par (str "throw new RuntimeException(\"AXIOM TO BE REALIZED (" ++ str s ++ str ")\")")
  | MLuint _ ->
    pp_par par (str "throw new RuntimeException(\"EXTRACTION OF UINT NOT IMPLEMENTED\")")
  | MLfloat _ ->
    pp_par par (str "throw new RuntimeException(\"EXTRACTION OF FLOAT NOT IMPLEMENTED\")")
  | MLstring _ ->
    pp_par par (str "throw new RuntimeException(\"EXTRACTION OF STRING NOT IMPLEMENTED\")")
  | MLparray _ ->
    pp_par par (str "throw new RuntimeException(\"EXTRACTION OF ARRAY NOT IMPLEMENTED\")")

and pp_expr_rel ctx par args n =
  let id = get_db_name n ctx.env in
  (* Try to survive to the occurrence of a Dummy rel.
     TODO: we should get rid of this hack (cf. BZ#592) *)
  let id = if Id.equal id dummy_name then Id.of_string "__" else id in
  (* A bare variable reference is always self-relative - see
     [is_self_relative_call]. *)
  pp_apply_typed ctx (pr_id id) (get_db_type n ctx.tenv) true par args

and pp_expr_lam ctx par args a =
  let fl,a' = collect_lams a in
  let fl,ctx' = ctx_push_vars (List.map id_of_mlid fl) ctx in
  let ctx' = ctx_ext_tenv (List.map (fun _ -> None) fl) ctx' in
  let st = pp_abst (List.rev fl) ++ pp_expr ctx' false [] a' in
  pp_apply2 ctx st par args

and pp_expr_letin ctx par args id a1 a2 =
  let i,ctx' = ctx_push_vars [id_of_mlid id] ctx in
  let ctx' = ctx_ext_tenv [None] ctx' in
  let pp_id = pr_id (List.hd i)
  and pp_a1 = pp_expr ctx false [] a1
  and pp_a2 = pp_expr ctx' false [] a2 in
  pp_apply2 ctx
    (hv 0 (str "{ val " ++ hov 2 (pp_id ++ str " =" ++ spc () ++ pp_a1) ++
           str ";" ++ spc () ++ pp_a2 ++ str " }"))
    par args

and pp_expr_glob ctx par args r =
  (* A self-recursive call prints its own type parameters explicitly:
     Scala cannot infer them from a call to a [def] whose own signature
     is still open at that point. *)
  let self_relative = is_self_call ctx.self (MLglob r) in
  let st =
    match ctx.self with
    | Some (_, vl) when self_relative -> pp_global ctx.table Term r ++ pp_type_params vl
    | _ -> pp_global ctx.table Term r
  in
  pp_apply_typed ctx st (find_glob_type r) self_relative par args

and pp_expr_cons ctx c r a =
  match a with
  | _ when is_native_char c -> pp_native_char c
  | _ when is_native_string c -> pp_native_string c
  | [] when is_inline_custom r ->
    (* A custom replacement (e.g. via [Extract Inductive]) need not be
       an applyable name (e.g. a literal like ["true"]). *)
    pp_global ctx.table Cons r
  | _ ->
    let pp_args = match find_cons_fields r with
      | None -> List.map (fun arg -> pp_expr ctx false [] arg) a
      | Some (nparams, fts) ->
        let inst, unsafe = discover_field_instantiation ctx nparams fts a in
        List.map2
          (fun ft arg ->
             let pp_arg = pp_expr ctx false [] arg in
             match field_cast_decision ctx unsafe inst ft arg with
             | FieldNoCast -> pp_arg
             | FieldCastAny ft ->
               str "(" ++ pp_arg ++ str ").asInstanceOf[" ++
               pp_any_instantiated_type ctx ft ++ str "]"
             | FieldCastTo ft ->
               str "(" ++ pp_arg ++ str ").asInstanceOf[" ++
               pp_type ctx.table false [] ft ++ str "]")
          fts a
    in
    let cons = pp_global ctx.table Cons r ++ str "(" ++
      prlist_with_sep (fun () -> str ", ") identity pp_args ++ str ")"
    in
    (* Delayed via [RocqLazy]; forced back where [MLcase] reads a
       coinductive scrutinee (see [pp_expr_case]). *)
    if is_coinductive (State.get_table ctx.table) r
    then str "RocqLazy(" ++ cons ++ str ")"
    else cons

and pp_expr_custom_match ctx par args t pv =
  if not (is_regular_match pv) then
    user_err Pp.(str "Cannot mix yet user-given match and general patterns.");
  let mkfun (ids,_,e) =
    if not (List.is_empty ids) then named_lams (List.rev ids) e
    else dummy_lams (ast_lift 1 e) 1
  in
  (* Scala has no bare juxtaposition application: every argument to the
     user-supplied match function - each branch, then the scrutinee -
     needs its own [(...)]. The match-function string itself stays
     unparenthesized: like any other `Extract` replacement, it is on
     the user to give it as an already-parenthesized curried lambda.

     [inner] additionally gets one unconditional pair of parens on top
     of the per-piece ones, not the usual [par]-gated one: Scala
     inserts a statement-terminating semicolon after a closing paren
     followed by a newline unless still inside an open bracket. Printed
     unwrapped where [par] happens to be false, this chain would
     silently split into unrelated statements - no error, just the
     last one's value (verified against a real `scalac`). *)
  let pp_branch tr = str "(" ++ pp_expr ctx true [] (mkfun tr) ++ str ")" ++ fnl () in
  let inner =
    str "(" ++
    hov 2 (str (find_custom_match pv) ++ fnl () ++
           prvect pp_branch pv ++
           str "(" ++ pp_expr ctx true [] t ++ str ")") ++
    str ")"
  in
  pp_apply2 ctx inner par args

and pp_expr_case ctx par args typ t pv =
  (* First, can this match be printed as a mere record field
     projection? See [record_proj_shape]/[pp_record_proj]. *)
  try pp_record_proj ctx par typ t pv args
  with Impossible ->
  let coind = is_coinductive_type (State.get_table ctx.table) typ in
  let head =
    if not coind then pp_expr ctx true [] t
    else
      let pp_t = pp_expr ctx true [] t in
      (* Forcing straight off [t], no cast, is sound exactly when [t]
         already provably has type [typ]; short of that,
         [pp_coinductive_force_target] gives a cast target precise
         enough that the matched fields never get a skolem type. *)
      if already_satisfies ctx t typ then pp_t ++ str ".force"
      else pp_t ++ str ".asInstanceOf[" ++
           pp_coinductive_force_target ctx typ ++ str "].force"
  in
  pp_apply2 ctx
    (v 0 (head ++ str " match {" ++ fnl () ++ pp_pat ctx typ pv ++ fnl () ++ str "}"))
    par args

(* Mirrors OCaml's [pp_record_proj]: prints a [match] that does nothing
   but read out a bound field (possibly applied to further arguments) as
   a plain [t.field] instead - a readability nicety, never a correctness
   fix (the ordinary [match] printing this falls back to on
   [Impossible] is always correct on its own). All the shape analysis
   already happened in [record_proj_shape]; only printing is left. *)
and pp_record_proj ctx par typ t pv args =
  match record_proj_shape ctx typ pv with
  | None -> raise Impossible
  | Some (fields, ids, pat, r, idx, a) ->
    let _, ctx' = ctx_push_vars (List.rev_map id_of_mlid ids) ctx in
    let ctx' = ctx_ext_tenv (branch_tenv_ext typ pat ids) ctx' in
    let pp_a = List.map (fun a -> (a, pp_expr ctx' true [] a)) a in
    let field_ty =
      match pattern_field_types typ r with
      | Some fts when idx < List.length fts -> Some (List.nth fts idx)
      | _ -> None
    in
    let pp_head =
      pp_expr ctx true [] t ++ str "." ++ pp_field ctx.table r fields idx
    in
    pp_apply_typed ctx pp_head field_ty (Option.has_some field_ty) par (pp_a @ args)

(* Unlike Haskell, a Scala constructor pattern is always printed as a
   call [Cons(args)], never bare juxtaposition, so it never needs
   parentheses of its own - there is no [par] parameter here. *)
and pp_cons_pat ctx r ppl =
  match ppl with
  | [] when is_inline_custom r ->
    (* As for the term-level [MLcons] case: e.g. a literal like ["true"]. *)
    pp_global ctx.table Cons r
  | _ ->
    pp_global ctx.table Cons r ++ str "(" ++ prlist_with_sep (fun () -> str ", ") identity ppl ++ str ")"

and pp_gen_pat ctx ids = function
  | Pcons (r,l) -> pp_cons_pat ctx r (List.map (pp_gen_pat ctx ids) l)
  | Pusual r -> pp_cons_pat ctx r (List.map pr_id ids)
  | Ptuple l -> str "(" ++ prlist_with_sep (fun () -> str ", ") (pp_gen_pat ctx ids) l ++ str ")"
  | Pwild -> str "_"
  | Prel n -> pr_id (get_db_name n ctx.env)

(* A [Pusual r] pattern's bound fields get their real type in [tenv] via
   [pattern_field_types]. Every other pattern shape stays [Any]-erased
   ([None]); only [tenv]'s length needs to stay in lockstep with
   [env]'s. *)
and pp_one_pat ctx typ (ids,p,t) =
  let ids',ctx' = ctx_push_vars (List.rev_map id_of_mlid ids) ctx in
  let ctx' = ctx_ext_tenv (branch_tenv_ext typ p ids) ctx' in
  hov 2 (str "case " ++
         pp_gen_pat ctx' (List.rev ids') p ++
         str " =>" ++ spc () ++
         pp_expr ctx' (expr_needs_par t) [] t)

and pp_pat ctx typ pv =
  prvecti
    (fun i x ->
       pp_one_pat ctx typ pv.(i) ++
       if Int.equal i (Array.length pv - 1) then mt () else fnl ())
    pv

(* Non-recursive top-level value binding ([Dterm]). [typed_signature]
   succeeding gives real parameter/return types and a [def] (if
   genuinely polymorphic - [val] can't carry type parameters) or a
   plain [val]; failing falls back to an unascribed [val]. Always sets
   [self] to [Some (None, vl)] once typed (never [Some r]: a [Dterm]
   never self-references), so its own type parameters remain
   available to [pp_cast_target]. *)
and pp_value_binding ctx name typ t =
  let bl,t' = collect_lams t in
  let bl,ctx0 = ctx_push_vars (List.map id_of_mlid bl) ctx in
  let n = List.length bl in
  match typed_signature typ n with
  | None ->
    let ctx' = ctx_ext_tenv (List.map (fun _ -> None) bl) { ctx0 with self = None } in
    hov 2 (str "val " ++ name ++ str " =" ++ spc () ++
           pp_abst (List.rev bl) ++
           pp_body_after_params bl (pp_expr ctx' false [] t'))
  | Some (vl, doms, rest) ->
    let self = Some (None, vl) in
    let ctx' = ctx_ext_tenv (List.rev_map (fun t -> Some t) doms) { ctx0 with self } in
    let kw = if List.is_empty vl then str "val " else str "def " in
    let pp_body = pp_expr ctx' false [] t' in
    let body =
      if already_satisfies ctx' t' rest then pp_body
      else str "(" ++ pp_body ++ str ").asInstanceOf[" ++ pp_type ctx.table false vl rest ++ str "]"
    in
    hov 2 (kw ++ name ++ pp_type_params vl ++ str ": " ++
           pp_type ctx.table false vl typ ++ str " =" ++ spc () ++
           pp_abst_typed ctx' vl (List.combine (List.rev bl) doms) ++
           pp_body_after_params bl body)

(* Recursive definitions need an explicit ascribed type (Scala can't
   infer a recursive [def]'s return type). Top-level [Dfix] passes its
   real stored type and gets the [pp_value_binding] treatment; a local
   [MLfix] (from [pp_fix] below) passes [Tunknown], always failing over
   to the uniform arity-only chain. [r_opt] is [Some] only for a genuine
   top-level [Dfix]; once typed, [self] becomes [Some (r_opt, vl)],
   replacing whatever was inherited (mutual recursion between different
   [Dfix] members doesn't get this treatment). *)
and pp_fix_function ctx r_opt name typ t =
  let bl,t' = collect_lams t in
  let bl,ctx0 = ctx_push_vars (List.map id_of_mlid bl) ctx in
  let n = List.length bl in
  match typed_signature typ n with
  | None ->
    let ctx' = ctx_ext_tenv (List.map (fun _ -> None) bl) ctx0 in
    if Int.equal n 0 then
      hov 2 (str "lazy val " ++ name ++ str ": Any =" ++ spc () ++
             pp_expr ctx' false [] t')
    else
      hov 2 (str "def " ++ name ++ str ": " ++ pp_any_chain n ++ str " =" ++ fnl () ++
             str "  " ++ pp_abst (List.rev bl) ++
             pp_body_after_params bl (pp_expr ctx' false [] t'))
  | Some (vl, doms, rest) ->
    let self' = Some (r_opt, vl) in
    let ctx' = ctx_ext_tenv (List.rev_map (fun t -> Some t) doms) { ctx0 with self = self' } in
    let pp_body = pp_expr ctx' false [] t' in
    let body =
      if already_satisfies ctx' t' rest then pp_body
      else str "(" ++ pp_body ++ str ").asInstanceOf[" ++ pp_type ctx.table false vl rest ++ str "]"
    in
    hov 2 (str "def " ++ name ++ pp_type_params vl ++ str ": " ++
           pp_type ctx.table false vl typ ++ str " =" ++ fnl () ++
           str "  " ++ pp_abst_typed ctx' vl (List.combine (List.rev bl) doms) ++
           pp_body_after_params bl body)

(*s Names of the functions ([ids]) are already pushed in [ctx], passed
    here just for convenience. *)
and pp_fix ctx par i (ids,bl) args =
  pp_par par
    (v 0
       (str "{" ++ fnl () ++
        v 1 (str "  " ++
             prvect_with_sep (fun () -> fnl ())
               (fun (fi,ti) -> pp_fix_function ctx None (pr_id fi) Tunknown ti)
               (Array.map2 (fun a b -> a,b) ids bl)) ++
        fnl () ++
        str "  " ++ pp_apply ctx (pr_id ids.(i)) false args ++ fnl () ++
        str "}"))

(*s Pretty-printing of inductive types declaration. *)

let pp_logical_ind packet =
  pp_bracket_comment
    (Id.print packet.ip_typename ++ str " : logical inductive" ++ fnl () ++
     str "with constructors : " ++ prvect_with_sep spc Id.print packet.ip_consnames)
  ++ fnl ()

let pp_singleton table packet =
  let name = pp_global table Type packet.ip_typename_ref in
  let l = rename_tvars keywords packet.ip_vars in
  hov 2 (str "type " ++ name ++ pp_type_params l ++ str " =" ++ spc () ++
         pp_type table false l (List.hd packet.ip_types.(0))) ++ fnl () ++
  pp_comment (str "singleton inductive, whose constructor was " ++
              Id.print packet.ip_consnames.(0))

(* [co]: whether the inductive is coinductive. When it is, the [sealed
   trait]/[case class] hierarchy is named [__Name] and [Name] itself
   becomes a [RocqLazy[__Name]] alias, so a coinductive value is always
   wrapped, never a bare case class (see [pp_expr_cons]'s [RocqLazy]
   wrap and [pp_expr_case]'s [.force]). *)
let pp_one_ind table co p pl cv =
  let pl = rename_tvars keywords pl in
  let targs = pp_type_params pl in
  let typename = pp_global table Type p.ip_typename_ref in
  let rawname = if co then str "__" ++ typename else typename in
  let pp_constructor i typs =
    let cname = pp_global table Cons p.ip_consnames_ref.(i) in
    (* Fields get their real, precise Rocq type, directly from [typs]. *)
    let fields = List.mapi (fun j t -> str "_" ++ int (j+1) ++ str ": " ++ pp_type table false pl t) typs in
    hov 2 (str "final case class " ++ cname ++ targs ++ str "(" ++
           prlist_with_sep (fun () -> str ", ") identity fields ++
           str ") extends " ++ rawname ++ targs)
  in
  if Array.is_empty cv then
    hov 2 (str "type " ++ typename ++ targs ++ str " = Unit") ++
    spc () ++ pp_comment (str "empty inductive")
  else
    str "sealed trait " ++ rawname ++ targs ++ fnl () ++
    v 0 (prvecti (fun i typs -> pp_constructor i typs ++ fnl ()) cv) ++
    (if not co then mt ()
     else fnl () ++
          hov 2 (str "type " ++ typename ++ targs ++ str " = RocqLazy[" ++
                 rawname ++ targs ++ str "]"))

(* A record prints directly as a single, named-field case class rather
   than the generic [sealed trait]-plus-[case class] encoding, plus a
   thin type alias when the record's type name and constructor name
   differ (the usual case). *)
let pp_record table fields packet =
  let ind = packet.ip_typename_ref in
  let typename = pp_global table Type ind in
  let cname = pp_global table Cons packet.ip_consnames_ref.(0) in
  let pl = rename_tvars keywords packet.ip_vars in
  let targs = pp_type_params pl in
  let fieldnames = pp_fields table ind fields in
  let l = List.combine fieldnames packet.ip_types.(0) in
  let decl =
    hov 2 (str "final case class " ++ cname ++ targs ++ str "(" ++
           prlist_with_sep (fun () -> str ", ")
             (fun (fname,t) -> fname ++ str ": " ++ pp_type table false pl t) l ++
           str ")")
  in
  if String.equal (Pp.string_of_ppcmds cname) (Pp.string_of_ppcmds typename) then decl
  else
    decl ++ fnl () ++
    hov 2 (str "type " ++ typename ++ targs ++ str " = " ++ cname ++ targs)

let rec pp_ind table co first i ind =
  if i >= Array.length ind.ind_packets then
    if first then mt () else fnl ()
  else
    let p = ind.ind_packets.(i) in
    let ip = p.ip_typename_ref in
    if is_custom ip then pp_ind table co first (i+1) ind
    else
      if p.ip_logical then
        pp_logical_ind p ++ pp_ind table co first (i+1) ind
      else
        pp_one_ind table co p p.ip_vars p.ip_types ++ fnl () ++
        pp_ind table co false (i+1) ind

(*s Pretty-printing of a declaration. *)

let pp_mind table i = match i.ind_kind with
  | Singleton -> pp_singleton table i.ind_packets.(0) ++ fnl ()
  | Record fields -> pp_record table fields i.ind_packets.(0) ++ fnl2 ()
  | Coinductive -> hov 0 (pp_ind table true true 0 i)
  | Standard -> hov 0 (pp_ind table false true 0 i)

(* An [Extract Constant]-replaced ([is_custom], not [is_inline_custom])
   [Dfix]/[Dterm]'s own declaration: ascribed with its real, precise
   Miniml type whenever [typed_signature] can decompose one, even
   though the printed *body* is just the user's raw replacement text.
   [find_glob_type] registers every [Dfix]/[Dterm]'s type
   unconditionally, customized or not, so every caller elsewhere in the
   file already calls [name] uncast whenever its type is real and not
   [Any]. Printing the binding itself as [: Any] regardless would make
   those calls a type error: a value statically typed [Any] has no
   [apply] method, so `mul(n)` fails to compile the moment anything
   calls a customized constant the ordinary way. Falls back to [Any]
   only when [typed_signature] can't decompose the type at all
   ([Taxiom]/[Tunknown]). *)
let pp_custom_binding table name typ replacement =
  (* [str " "], not the breakable [spc ()]: a replacement string is
     opaque user text that Format could wrap onto a deeper-indented
     continuation line, and under Scala 3's significant indentation
     that opens an *implicit indented block* swallowing every following
     sibling declaration into this one's value (verified against a
     real `scalac`: it silently drops them). Keeping it on one physical
     line, however long, avoids the ambiguity. *)
  match typed_signature typ 0 with
  | None -> str "def " ++ name ++ str ": Any =" ++ str " " ++ str replacement
  | Some (vl, _, rest) ->
    let kw = if List.is_empty vl then str "val " else str "def " in
    kw ++ name ++ pp_type_params vl ++ str ": " ++ pp_type table false vl rest ++
    str " =" ++ str " " ++ str replacement

let pp_decl table = function
  | Dind i -> pp_mind table i
  | Dtype (r, l, t) ->
      if is_inline_custom r then mt ()
      else
        let l = rename_tvars keywords l in
        let st =
          try
            let ids,s = find_type_custom r in
            (match ids with
             | [] -> mt ()
             | _ -> str "[" ++ prlist_with_sep (fun () -> str ", ") str ids ++ str "]") ++
            str " =" ++ spc () ++ str s
          with Not_found ->
            pp_type_params l ++
            (if t == Taxiom then
               str " =" ++ spc () ++ str "Any" ++ spc () ++
               pp_bracket_comment (str "AXIOM TO BE REALIZED")
             else str " =" ++ spc () ++ pp_type table false l t)
        in
        hov 2 (str "type " ++ pp_global table Type r ++ st) ++ fnl2 ()
  | Dfix (rv, defs, typs) ->
      let names = Array.map
        (fun r -> if is_inline_custom r then mt () else pp_global table Term r) rv
      in
      prvecti
        (fun i r ->
          let void = is_inline_custom r ||
            (not (is_custom r) &&
             match defs.(i) with MLexn "UNUSED" -> true | _ -> false)
          in
          if void then mt ()
          else
            (if is_custom r then
               pp_custom_binding table names.(i) typs.(i) (find_custom r)
             else
               pp_fix_function (init_ctx table) (Some r) names.(i) typs.(i) defs.(i))
            ++ fnl2 ())
        rv
  | Dterm (r, a, t) ->
      if is_inline_custom r then mt ()
      else
        let e = pp_global table Term r in
        if is_custom r then
          pp_custom_binding table e t (find_custom r) ++ fnl2 ()
        else
          hov 0 (pp_value_binding (init_ctx table) e t a ++ fnl2 ())

let rec pp_structure_elem table = function
  | (_,SEdecl d) -> pp_decl table d
  | (_,SEmodule m) -> pp_module_expr table m.ml_mod_expr
  | (_,SEmodtype _) -> mt ()
      (* for the moment we simply discard module types *)

and pp_module_expr table = function
  | MEstruct (_,sel) -> prlist_strict (fun e -> pp_structure_elem table e) sel
  | MEfunctor _ -> mt ()
      (* for the moment we simply discard unapplied functors *)
  | MEident _ | MEapply _ -> assert false
      (* should be expanded in extract_env *)

(* Closes the [object] opened by [preamble]. *)
let pp_struct table s =
  struct_info := register_structure s;
  let pp_sel (mp,sel) = State.with_visibility table mp [] begin fun table ->
    prlist_strict (fun e -> pp_structure_elem table e) sel
  end in
  prlist_strict pp_sel s ++ str "}" ++ fnl ()

let file_naming state mp = file_of_modfile (State.get_table state) mp

let scala_descr = {
  keywords = keywords;
  file_suffix = ".scala";
  file_naming = file_naming;
  preamble = preamble;
  pp_struct = pp_struct;
  sig_suffix = None;
  sig_preamble = (fun _ _ _ _ _ -> mt ());
  pp_sig = (fun _ _ -> mt ());
  pp_decl = pp_decl;
}
