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
open CAst
open Names
open Libnames
open Tac2expr
open Tac2subst

let check_lowercase {loc;v=id} =
  if Tac2env.is_constructor (Libnames.qualid_of_ident id) then
    CErrors.user_err ?loc Pp.(str "The identifier " ++ Id.print id ++ str " must start with a lowercase letter.")

let internal_ltac2_expr = Procq.Entry.make "ltac2_expr"

module Tac2Custom = KerName

module CustomV = struct
  include Tac2Custom
  let is_var _ = None
  let stage = Summary.Stage.Synterp
  let summary_name = "ltac2_customentrytab"
end
module CustomTab = Nametab.EasyNoWarn(CustomV)()

let ltac2_custom_map : raw_tacexpr Procq.Entry.t Tac2Custom.Map.t Procq.GramState.field =
  Procq.GramState.field "ltac2_custom_map"

let ltac2_custom_entry : (Tac2Custom.t, raw_tacexpr) Procq.entry_command =
  Procq.create_entry_command "ltac2" {
    eext_fun = (fun kn e state ->
      let map = Option.default Tac2Custom.Map.empty (Procq.GramState.get state ltac2_custom_map) in
      let map = Tac2Custom.Map.add kn e map in
      Procq.GramState.set state ltac2_custom_map map);
    eext_name = (fun kn -> "custom-ltac2:" ^ Tac2Custom.to_string kn);
    eext_eq = Tac2Custom.equal;
  }

let find_custom_entry kn =
  Tac2Custom.Map.get kn @@ Option.get @@ Procq.GramState.get (Procq.gramstate()) ltac2_custom_map

let () =
  Metasyntax.register_custom_grammar_for_print @@ fun name ->
  match CustomTab.locate name with
  | exception Not_found -> None
  | name -> Some [Any (find_custom_entry name)]

let load_custom_entry i ((sp,kn),local) =
  let () = CustomTab.push (Until i) sp kn in
  let () = Procq.extend_entry_command ltac2_custom_entry kn in
  let () = assert (not local) in
  ()

let import_custom_entry i ((sp,kn),local) =
  let () = CustomTab.push (Exactly i) sp kn in
  ()

let cache_custom_entry o =
  load_custom_entry 1 o;
  import_custom_entry 1 o

let inCustomEntry : Id.t -> bool -> Libobject.obj =
  let open Libobject in
  declare_named_object {
    (default_object "Ltac2 custom entry") with
    object_stage = Synterp;
    cache_function = cache_custom_entry;
    load_function = load_custom_entry;
    open_function = filtered_open import_custom_entry;
    subst_function = (fun (_,x) -> x);
    classify_function = (fun local -> if local then Dispose else Substitute);
  }

module Syntax = struct

  module DynEntry = Dyn.Make()

  module EntryMap = DynEntry.Map(struct type 'a t = 'a Procq.Entry.t end)

  let entries = ref EntryMap.empty

  (* NB someday we may want to allow registering more custom entry kinds
     instead of handling custom constr and custom ltac2 specially *)
  type 'a entry =
    | RegisteredEntry of 'a DynEntry.tag
    | CustomConstr : Globnames.CustomName.t -> Constrexpr.constr_expr entry
    | CustomLtac2 : Tac2Custom.t -> raw_tacexpr entry

  let register_entry ?name entry =
    let name = Option.default (Procq.Entry.name entry) name in
    let tag = DynEntry.create name in
    entries := EntryMap.add tag entry !entries;
    RegisteredEntry tag

  let get_entry : type a. a entry -> a Procq.Entry.t = function
    | RegisteredEntry e -> EntryMap.find e !entries
    | CustomConstr e -> fst @@ Egramrocq.find_custom_entry e
    | CustomLtac2 e -> find_custom_entry e

  let entry_equal : type a b. a entry -> b entry -> (a, b) Util.eq option = fun a b ->
    match a, b with
    | RegisteredEntry a, RegisteredEntry b -> DynEntry.eq a b
    | CustomConstr a, CustomConstr b ->
      if Globnames.CustomName.equal a b then Some Refl else None
    | CustomLtac2 a, CustomLtac2 b ->
      if Tac2Custom.equal a b then Some Refl else None
    | (RegisteredEntry _ | CustomConstr _ | CustomLtac2 _), _ -> None

  let entry_compare : type a b. a entry -> b entry -> int = fun a b ->
    match a, b with
    | RegisteredEntry a, RegisteredEntry b -> DynEntry.compare a b
    | RegisteredEntry _, _ -> -1
    | _, RegisteredEntry _ -> 1
    | CustomConstr a, CustomConstr b -> Globnames.CustomName.compare a b
    | CustomConstr _, _ -> -1
    | _, CustomConstr _ -> 1
    | CustomLtac2 a, CustomLtac2 b -> Tac2Custom.compare a b

  type 'a t =
    | NTerm of 'a entry
    | NTerml of 'a entry * string
    | List0 : 'a t * string option -> 'a list t
    | List1 : 'a t * string option -> 'a list t
    | Opt : 'a t -> 'a option t
    | Self : raw_tacexpr t
    | Next : raw_tacexpr t
    | Token of 'a Tok.p
    | Tokens : Procq.ty_pattern list -> unit t
    | Seq of 'a seq

  and _ seq =
    | Nil : unit seq
    | Snoc : 'a seq * 'b t -> ('a * 'b) seq
    (* We use snoc lists for seq because that works better when translating to Procq.Rule.t
       (the same argument is on the outside of the tuple ['r] and of the function type ['f]) *)

  type _ rec_ =
    | NoRec : Gramlib.Grammar.norec rec_
    | MayRec

  type 'a symbol = Symb : 'mayrec rec_ * (raw_tacexpr, 'mayrec, 'a) Procq.Symbol.t -> 'a symbol

  (* Procq.Rule.t contains the type ['fulla] parsed by the whole seq in it last argument.
     We connect it to the type ['a] involved in the head of the seq using this GADT.
     (and also handle mayrec) *)
  type ('a,'fulla) rule =
      Rule :
        'mayrec rec_ *
        (('a -> Loc.t -> 'fulla) -> 'f) *
        (raw_tacexpr, 'mayrec, 'f, Loc.t -> 'fulla) Procq.Rule.t ->
        ('a,'fulla) rule

  let norec s = Symb (NoRec, s)

  let rec to_symbol : type a. a t -> a symbol = fun s ->
    let open Procq.Symbol in
    match s with
    | NTerm e -> norec @@ nterm (get_entry e)
    | NTerml (e, lev) -> norec @@ nterml (get_entry e) lev
    | List0 (s, None) ->
      let Symb (mayrec, s) = to_symbol s in
      Symb (mayrec, list0 s)
    | List0 (s, Some sep) ->
      let Symb (mayrec, s) = to_symbol s in
      let sep = tokens [TPattern (CLexer.terminal sep)] in
      Symb (mayrec, list0sep s sep)
    | List1 (s, None) ->
      let Symb (mayrec, s) = to_symbol s in
      Symb (mayrec, list1 s)
    | List1 (s, Some sep) ->
      let Symb (mayrec, s) = to_symbol s in
      let sep = tokens [TPattern (CLexer.terminal sep)] in
      Symb (mayrec, list1sep s sep)
    | Opt s ->
      let Symb (mayrec, s) = to_symbol s in
      Symb (mayrec, opt s)
    | Self -> Symb (MayRec, self)
    | Next -> Symb (MayRec, next)
    | Token p -> norec @@ token p
    | Tokens l -> norec @@ tokens l
    | Seq s -> seq_to_symbol s

  and seq_to_rule : type a fulla. a seq -> (a,fulla) rule =
    fun s ->
    match s with
    | Nil -> Rule (NoRec, (fun f (loc:Loc.t) -> f () loc), Procq.Rule.stop)
    | Snoc (hd, x) ->
      let Rule (rechd, f, hd) = seq_to_rule hd in
      let Symb (recx, x) = to_symbol x in
      let f (g:a -> Loc.t -> fulla) x = f (fun hd loc -> g (hd, x) loc) in
      match rechd, recx with
      | NoRec, NoRec ->
        let rule = Procq.Rule.next_norec hd x in
        Rule (NoRec, f, rule)
      | MayRec, _ | _, MayRec ->
        let rule = Procq.Rule.next hd x in
        Rule (MayRec, f, rule)

  and seq_to_symbol : type a. a seq -> a symbol = fun s ->
    let open Procq.Symbol in
    let Rule (mayrec, f, r) = seq_to_rule s in
    match mayrec with
    | MayRec ->
      CErrors.user_err Pp.(str "Recursive symbols (self / next) are not allowed in local rules.")
    | NoRec -> norec @@ rules [Procq.Rules.make r (f (fun (x:a) (_:Loc.t) -> x))]

  let constr = register_entry Procq.Constr.constr
  let lconstr = register_entry Procq.Constr.lconstr
  let term = register_entry Procq.Constr.term

  let custom_constr c = CustomConstr c
  let custom_ltac2 c = CustomLtac2 c

  let ltac2_expr = register_entry internal_ltac2_expr

  let nterm e = NTerm e
  let nterml e lev = NTerml (e, lev)
  let list0 ?sep s = List0 (s, sep)
  let list1 ?sep s = List1 (s, sep)
  let opt s = Opt s
  let self = Self
  let next = Next
  let token p = Token p
  let tokens l = Tokens l

  let seq s = Seq s
  let nil = Nil
  let snoc a b = Snoc (a, b)

  let rec equal : type a b. a t -> b t -> (a, b) Util.eq option = fun a b ->
    match a, b with
    | NTerm a, NTerm b -> entry_equal a b
    | NTerml (a, leva), NTerml (b, levb) ->
      let e = entry_equal a b in
      if Option.has_some e && String.equal leva levb then e
      else None
    | List0 (a, sepa), List0 (b, sepb) ->
      begin match equal a b with
      | None -> None
      | Some Refl -> if Option.equal String.equal sepa sepb then Some Refl else None
      end
    | List1 (a, sepa), List1 (b, sepb) ->
      begin match equal a b with
      | None -> None
      | Some Refl -> if Option.equal String.equal sepa sepb then Some Refl else None
      end
    | Opt a, Opt b ->
      begin match equal a b with
      | None -> None
      | Some Refl -> Some Refl
      end
    | Self, Self -> Some Refl
    | Next, Next -> Some Refl
    | Token a, Token b -> Tok.equal_p a b
    | Tokens a, Tokens b ->
      let eq (Procq.TPattern p1) (Procq.TPattern p2) = Option.has_some (Tok.equal_p p1 p2) in
      if CList.for_all2eq eq a b then Some Refl else None
    | Seq s1, Seq s2  -> equal_seq s1 s2
    | (NTerm _ | NTerml _ | List0 _ | List1 _ | Opt _
      | Self | Next | Token _ | Tokens _ | Seq _), _ ->
      None

  and equal_seq : type a b. a seq -> b seq -> (a, b) Util.eq option = fun a b ->
    match a, b with
    | Nil, Nil -> Some Refl
    | Snoc (a1, a2), Snoc (b1, b2) ->
      begin match equal_seq a1 b1 with
      | None -> None
      | Some Refl -> match equal a2 b2 with
        | None -> None
        | Some Refl -> Some Refl
      end
    | (Nil | Snoc _), _ -> None

  let rec compare : type a b. a t -> b t -> int = fun a b ->
    match a, b with
    | NTerm a, NTerm b -> entry_compare a b
    | NTerm _, _ -> -1
    | _, NTerm _ -> 1
    | NTerml (a, leva), NTerml (b, levb) ->
      let e = entry_compare a b in
      if e <> 0 then e else String.compare leva levb
    | NTerml _, _ -> -1
    | _, NTerml _ -> 1
    | List0 (a, sepa), List0 (b, sepb) ->
      begin match compare a b with
      | 0 -> Option.compare String.compare sepa sepb
      | c -> c
      end
    | List0 _, _ -> -1
    | _, List0 _ -> 1
    | List1 (a, sepa), List1 (b, sepb) ->
      begin match compare a b with
      | 0 -> Option.compare String.compare sepa sepb
      | c -> c
      end
    | List1 _, _ -> -1
    | _, List1 _ -> 1
    | Opt a, Opt b -> compare a b
    | Opt _, _ -> -1
    | _, Opt _ -> 1
    | Self, Self -> 0
    | Self, _ -> -1
    | _, Self -> 1
    | Next, Next -> 0
    | Next, _ -> -1
    | _, Next -> 1
    (* XXX treating [PIDENT (Some s)] and [PKEYWORD s] as equal may be
       questionable, consider moving Tok.compare_p to this file (only
       user at this time) and comparing them to be different
       (AFAICT compare = 0 -> equal = Some Refl is the more important invariant,
       we don't care as much about the other direction) *)
    | Token a, Token b -> Tok.compare_p a b
    | Token _, _ -> -1
    | _, Token _ -> 1
    | Tokens a, Tokens b ->
      let cmp (Procq.TPattern p1) (Procq.TPattern p2) = Tok.compare_p p1 p2 in
      CList.compare cmp a b
    | Tokens _, _ -> -1
    | _, Tokens _ -> 1
    | Seq s1, Seq s2  -> compare_seq s1 s2

  and compare_seq : type a b. a seq -> b seq -> int = fun a b ->
    match a, b with
    | Nil, Nil -> 0
    | Nil, _ -> -1
    | _, Nil -> 1
    | Snoc (a1, a2), Snoc (b1, b2) ->
      begin match compare_seq a1 b1 with
      | 0 -> compare a2 b2
      | c -> c
      end
end

module ParsedNota = struct
  (* parsing rule + which entry it is in *)
  (* XXX also include level? *)
  type 'a t = 'a Syntax.seq * Tac2Custom.t option

  type any = Any : _ t -> any

  let compare (a1,a2) (b1,b2) =
    let c = Option.compare Tac2Custom.compare a2 b2 in
    if c <> 0 then c else Syntax.compare_seq a1 b1

  module Any = struct
    type t = any
    let compare (Any x) (Any y) = compare x y
  end
  module AnyMap = CMap.Make(Any)
end

module TacSyn = struct
  type t = WithArgs : 'a ParsedNota.t * 'a -> t

  let make (x:t) : tacsyn = Obj.magic x
  let get (x:tacsyn) : t = Obj.magic x

end

type 'a token =
| TacTerm of string
| TacNonTerm of Name.t * 'a

type syntax_class_rule =
| SyntaxRule : 'a Syntax.t * ('a -> raw_tacexpr) -> syntax_class_rule

type used_levels = Int.Set.t Tac2Custom.Map.t

let no_used_levels = Tac2Custom.Map.empty

let union_used_levels a b =
  Tac2Custom.Map.union (fun _ a b -> Some (Int.Set.union a b)) a b

(* hardcoded syntactic classes, from ltac2 or further plugins *)
type 'glb syntax_class_decl = {
  intern_synclass : sexpr list -> used_levels * 'glb;
  interp_synclass : 'glb -> syntax_class_rule;
}

module SynclassDyn = Dyn.Make()

type syntax_class = SynclassDyn.t

module SynclassInterpMap = SynclassDyn.Map(struct
    type 'a t = 'a -> syntax_class_rule
  end)

let syntax_class_interns : (sexpr list -> used_levels * SynclassDyn.t) Id.Map.t ref =
  ref Id.Map.empty

let syntax_class_interps = ref SynclassInterpMap.empty

let check_custom_entry_name id =
  (* XXX allow it anyway? the name can be accessed by qualifying it *)
  if Id.Map.mem id !syntax_class_interns then
    CErrors.user_err
      Pp.(str "Cannot declare " ++ Id.print id ++
          str " as a ltac2 custom entry:" ++ spc() ++
          str "that name is already used for a builtin syntactic class.")
  else if CustomTab.exists (Lib.make_path id) then
    CErrors.user_err Pp.(str "Ltac2 custom entry " ++ Id.print id ++ str " already exists.")

let register_custom_entry name =
  let name = name.CAst.v in
  check_custom_entry_name name;
  (* not yet implemented: module local custom entries
     NB: will need checks that exported notations don't rely on the local entries *)
  let local = false in
  Lib.add_leaf (inCustomEntry name local)

let register_syntax_class id (s:_ syntax_class_decl) =
  assert (not (Id.Map.mem id !syntax_class_interns));
  let tag = SynclassDyn.create (Id.to_string id) in
  let intern args =
    let used, data = s.intern_synclass args in
    used, SynclassDyn.Dyn (tag, data)
  in
  syntax_class_interns := Id.Map.add id intern !syntax_class_interns;
  syntax_class_interps := SynclassInterpMap.add tag s.interp_synclass !syntax_class_interps

let level_name lev = string_of_int lev

let terminal_synclass_tag : string SynclassDyn.tag = SynclassDyn.create "<terminal>"

let interp_terminal str : syntax_class_rule =
  let v_unit = CAst.make @@ CTacCst (AbsKn (Tuple 0)) in
  SyntaxRule (Syntax.token (Tok.PIDENT (Some str)), (fun _ -> v_unit))

let () =
  syntax_class_interps := SynclassInterpMap.add terminal_synclass_tag interp_terminal !syntax_class_interps

type custom_synclass_data = {
  custom_synclass_name : Tac2Custom.t;
  custom_synclass_level : int option;
}

let interp_custom_entry data : syntax_class_rule =
  let ename = data.custom_synclass_name in
  let entry = Syntax.custom_ltac2 ename in
  match data.custom_synclass_level with
  | None ->
    SyntaxRule (Syntax.nterm entry, (fun expr -> expr))
  | Some lev ->
    SyntaxRule (Syntax.nterml entry (level_name lev), (fun expr -> expr))

let custom_synclass_tag : custom_synclass_data SynclassDyn.tag = SynclassDyn.create "<custom>"

let () =
  syntax_class_interps := SynclassInterpMap.add custom_synclass_tag interp_custom_entry !syntax_class_interps

let intern_custom_entry ?loc qid ename args : used_levels * custom_synclass_data =
  let lev =
    match args with
    | [] -> None
    | [SexprInt {CAst.v=lev}] -> Some lev
    | _ :: _ ->
      CErrors.user_err ?loc
        Pp.(str "Invalid arguments for ltac2 custom entry " ++ pr_qualid qid ++ str ".")
  in
  let used = match lev with
    | None -> no_used_levels
    | Some lev -> Tac2Custom.Map.singleton ename (Int.Set.singleton lev)
  in
  used, { custom_synclass_name = ename;
    custom_synclass_level = lev;
  }

let intern_syntactic_class ?loc qid args =
  let is_class =
    if qualid_is_ident qid then Id.Map.find_opt (qualid_basename qid) !syntax_class_interns
    else None
  in
  match is_class with
  | Some intern -> intern args
  | None ->
    match CustomTab.locate qid with
    | kn ->
      let used, data = intern_custom_entry ?loc qid kn args in
      used, SynclassDyn.Dyn (custom_synclass_tag, data)
    | exception Not_found ->
      CErrors.user_err ?loc Pp.(str "Unknown syntactic class" ++ spc () ++ pr_qualid qid)

module ParseToken =
struct

let loc_of_token = function
| SexprStr {loc} -> loc
| SexprInt {loc} -> loc
| SexprRec (loc, _, _) -> Some loc

let intern_syntax_class = function
| SexprRec (_, {loc;v=Some id}, toks) ->
  intern_syntactic_class id toks
| SexprStr {v=str} -> no_used_levels, SynclassDyn.Dyn (terminal_synclass_tag, str)
| tok ->
  let loc = loc_of_token tok in
  CErrors.user_err ?loc Pp.(str "Invalid parsing token")

let check_name na =
  match na.CAst.v with
  | None -> Anonymous
  | Some id ->
    let id = if qualid_is_ident id then qualid_basename id
      else CErrors.user_err ?loc:id.loc Pp.(str "Must be an identifier.")
    in
    let () = check_lowercase (CAst.make ?loc:na.CAst.loc id) in
    Name id

let parse_token = function
| SexprStr {v=s} -> no_used_levels, TacTerm s
| SexprRec (_, na, [tok]) ->
  let na = check_name na in
  let used, syntax_class = intern_syntax_class tok in
  used, TacNonTerm (na, syntax_class)
| tok ->
  let loc = loc_of_token tok in
  CErrors.user_err ?loc Pp.(str "Invalid parsing token")

let rec print_syntax_class = let open Pp in function
| SexprStr s -> str s.CAst.v
| SexprInt i -> int i.CAst.v
| SexprRec (_, {v=na}, []) -> Option.cata pr_qualid (str "_") na
| SexprRec (_, {v=na}, e) ->
  Option.cata pr_qualid (str "_") na ++ str "(" ++ pr_sequence print_syntax_class e ++ str ")"

let print_token = let open Pp in function
| SexprStr {v=s} -> quote (str s)
| SexprRec (_, {v=na}, [tok]) -> print_syntax_class tok
| _ -> assert false

end

let intern_syntax_class = ParseToken.intern_syntax_class

type synext = {
  synext_used : used_levels;
  synext_tok : ParsedNota.any;
  synext_level : int;
  synext_local : bool;
}

let interp_syntax_class (SynclassDyn.Dyn (tag, data)) =
  let interp = SynclassInterpMap.find tag !syntax_class_interps in
  interp data

type any_seq = AnySeq : _ Syntax.seq -> any_seq

let rec get_nota_parsing (tok : SynclassDyn.t token list) : any_seq = match tok with
| [] -> AnySeq Nil
| TacNonTerm (_, v) :: tok ->
  let SyntaxRule (syntax_class, _) = interp_syntax_class v in
  let AnySeq rest = get_nota_parsing tok in
  AnySeq (Snoc (rest, syntax_class))
| TacTerm t :: tok ->
  let AnySeq rest = get_nota_parsing tok in
  AnySeq (Snoc (rest, Syntax.token (CLexer.terminal t)))

let deprecated_ltac2_notation =
  Deprecation.create_warning
    ~object_name:"Ltac2 notation"
    ~warning_name_if_no_since:"deprecated-ltac2-notation"
    Pp.(fun (toks : sexpr list) -> pr_sequence ParseToken.print_token toks)

let ltac2_levels = Procq.GramState.field "ltac2_levels"

(* XXX optional lev and do reusefirst like in egramrocq? *)
let fresh_level st entry lev =
  match entry with
  | None -> st, None
  | Some entry ->
    let all_levels = Option.default Tac2Custom.Map.empty @@ Procq.GramState.get st ltac2_levels in
    let entry_levels = Option.default Int.Set.empty @@ Tac2Custom.Map.find_opt entry all_levels in
    let last_before = Int.Set.find_first_opt (fun lev' -> lev' >= lev) entry_levels in
    if Option.equal Int.equal last_before (Some lev) then st, None
    else
      let pos = match last_before with
        | None -> Gramlib.Gramext.First
        | Some lev' -> Gramlib.Gramext.After (level_name lev')
      in
      let entry_levels = Int.Set.add lev entry_levels in
      let all_levels = Tac2Custom.Map.add entry entry_levels all_levels in
      let st = Procq.GramState.set st ltac2_levels all_levels in
      st, Some pos

let check_levels st used_levels =
  let all_levels = Option.default Tac2Custom.Map.empty @@ Procq.GramState.get st ltac2_levels in
  let iter kn used =
    let known = Option.default Int.Set.empty (Tac2Custom.Map.find_opt kn all_levels) in
    let missing = Int.Set.diff used known in
    if not (Int.Set.is_empty missing) then
      CErrors.user_err
        Pp.(str "Unknown " ++ str (String.plural (Int.Set.cardinal missing) "level") ++
            str " for ltac2 custom entry " ++ CustomTab.pr kn)
  in
  Tac2Custom.Map.iter iter used_levels

let perform_notation syn st =
  let Any parsing = syn.synext_tok in
  let used = syn.synext_used in
  let rule, entry = parsing in
  let Rule (_, f, rule) = Syntax.seq_to_rule rule in
  let g args loc =
    CAst.make ~loc @@ CTacSyn (TacSyn.make @@ WithArgs (parsing, args))
  in
  let rule = Procq.Production.make rule (f g) in
  let lev = syn.synext_level in
  let st, fresh = fresh_level st entry lev in
  let () = check_levels st used in
  let pos = Some (level_name lev) in
  let rule = match fresh with
    | None -> Procq.Reuse (pos, [rule])
    | Some pos' ->
      (* BothA means we can have SELF on both the left and right of a rule. *)
      Procq.Fresh (pos', [pos, Some BothA, [rule]])
  in
  let entry = match entry with
    | None -> internal_ltac2_expr
    | Some entry -> find_custom_entry entry
  in
  [Procq.ExtendRule (entry, rule)], st

let ltac2_notation =
  Procq.create_grammar_command "ltac2-notation" { gext_fun = perform_notation; gext_eq = (==) (* FIXME *) }

let cache_synext syn =
  Procq.extend_grammar_command ~ignore_kw:false ltac2_notation syn

(* XXX missing subst on custom entries, including recursively in SynclassDyn.t *)
let subst_synext (subst, syn) = syn

let ltac2_notation_cat = Libobject.create_category "ltac2.notations"

let inTac2Notation : synext -> Libobject.obj =
  let open Libobject in
  declare_object {(default_object "TAC2-NOTATION") with
     object_stage = Summary.Stage.Synterp;
     cache_function  = cache_synext;
     open_function   = simple_open ~cat:ltac2_notation_cat cache_synext;
     subst_function = subst_synext;
     classify_function = (fun o -> if o.synext_local then Dispose else Substitute);
  }

type notation_data =
  | UntypedNota of raw_tacexpr
  | TypedNota of {
      nota_prms : int;
      nota_argtys : int glb_typexpr Id.Map.t;
      nota_ty : int glb_typexpr;
      nota_body : glb_tacexpr;
    }

type 'body notation_interpretation = {
  nota_local : bool;
  (* sexpr used for printing deprecation message, XXX print the internalized version? *)
  nota_raw : sexpr list;
  nota_depr : Deprecation.t option;
  nota_parsing : ParsedNota.any;
  nota_tok : SynclassDyn.t token list;
  nota_body : 'body;
}

let notation_data = Summary.ref ~name:"tac2notation-data" ParsedNota.AnyMap.empty

let rec interp_notation_args : type a. a Syntax.seq -> _ -> a -> _ = fun parsing toks args ->
  match parsing, toks, args with
  | Nil, (_::_), ()
  | Snoc _, [], (_, _) -> assert false
  | Nil, [], () -> []
  | Snoc (hd, _), TacTerm _ :: toks, (args, _) -> interp_notation_args hd toks args
  | Snoc (hd, x), TacNonTerm (na, tok) :: toks, (args, arg) ->
    let SyntaxRule (x', inj) = interp_syntax_class tok in
    let Refl = match Syntax.equal x x' with
      | None -> assert false
      | Some e -> e
    in
    let arg = inj arg in
    (* XXX loc (only used for untyped notations though) *)
    (CAst.make na, arg) :: interp_notation_args hd toks args

(* to have scoped notations: add a scope stack argument here,
   per-scope notations in the notation_data map, and user syntax for
   scopes *)
let interp_notation ?loc syn
  : notation_data * (lname * raw_tacexpr) list =
  let WithArgs ((rule, _ as parsing), args) = TacSyn.get syn in
  let data : notation_data notation_interpretation =
    ParsedNota.AnyMap.get (Any parsing) !notation_data
  in
  let () = match data.nota_depr with
    | None -> ()
    | Some depr -> deprecated_ltac2_notation ?loc (data.nota_raw, depr)
  in
  let args = interp_notation_args rule data.nota_tok args in
  data.nota_body, args

let cache_synext_interp data =
  notation_data := ParsedNota.AnyMap.add data.nota_parsing data !notation_data

let subst_notation_data subst = function
  | UntypedNota body as n ->
    let body' = subst_rawexpr subst body in
    if body' == body then n else UntypedNota body'
  | TypedNota { nota_prms=prms; nota_argtys=argtys; nota_ty=ty; nota_body=body } as n ->
    let body' = subst_expr subst body in
    let argtys' = Id.Map.Smart.map (subst_type subst) argtys in
    let ty' = subst_type subst ty in
    if body' == body && argtys' == argtys && ty' == ty then n
    else TypedNota {nota_body=body'; nota_argtys=argtys'; nota_ty=ty'; nota_prms=prms}

(* XXX missing subst on custom entries, recursively in SynclassDyn.t *)
let subst_synext_interp (subst, data) =
  let body' = subst_notation_data subst data.nota_body in
  if body' == data.nota_body then data else
  { data with nota_body = body' }

let inTac2NotationInterp : _ -> Libobject.obj =
  let open Libobject in
  declare_object {(default_object "TAC2-NOTATION-INTERP") with
     cache_function  = cache_synext_interp;
     open_function   = simple_open ~cat:ltac2_notation_cat cache_synext_interp;
     subst_function = subst_synext_interp;
     classify_function = (fun data -> if data.nota_local then Dispose else Substitute);
}

type notation_target = {
  target_entry : qualid option;
  target_level : int option;
}

let pr_register_notation tkn target body =
  let open Pp in
  let pptarget = match target.target_entry, target.target_level with
    | None, None -> mt()
    | None, Some lev -> spc() ++ str ": " ++ int lev
    | Some entry, None -> spc() ++ str ": " ++ pr_qualid entry
    | Some entry, Some lev ->
      spc() ++ str ": " ++ pr_qualid entry ++ str "(" ++ int lev ++ str ")"
  in
  prlist_with_sep spc Tac2print.pr_syntax_class tkn ++
  pptarget ++ spc() ++
  hov 2 (str ":= " ++ Tac2print.pr_rawexpr_gen E5 ~avoid:Id.Set.empty body)

let tactic_qualid = qualid_of_ident (Id.of_string "tactic")

let register_notation atts tkn target body =
  let deprecation, local = Attributes.(parse Notations.(deprecation ++ locality)) atts in
  let local = Option.default false local in
  let entry = match target.target_entry with
    | Some entry ->
      if qualid_eq entry tactic_qualid then None
      else begin
        try Some (CustomTab.locate entry)
        with Not_found -> CErrors.user_err Pp.(str "Unknown entry " ++ pr_qualid entry ++ str ".")
      end
    | None -> None
  in
  (* Globalize so that names are absolute *)
  let lev = if Option.has_some entry then
      let lev = match target.target_level with
        | Some lev -> lev
        | None -> CErrors.user_err Pp.(str "Custom entry level must be explicit.")
      in
      let () = if lev < 0 then CErrors.user_err Pp.(str "Custom entry levels must be nonnegative.") in
      lev
    else match target.target_level with
      | Some n ->
        let () =
          if n < 0 || n > 6 then
            CErrors.user_err Pp.(str "Notation levels must range between 0 and 6")
        in
        n
      | None ->
        (* autodetect level *)
        begin match tkn with
        | SexprStr s :: _ when Names.Id.is_valid s.CAst.v -> 1
        | _ -> 5
        end
  in
  let tokens = List.rev_map ParseToken.parse_token tkn in
  let used, tokens = List.split tokens in
  let used = List.fold_left union_used_levels no_used_levels used in
  let AnySeq parsing = get_nota_parsing tokens in
  let parsing = ParsedNota.Any (parsing, entry) in
  let ext = {
    synext_used = used;
    synext_tok = parsing;
    synext_level = lev;
    synext_local = local;
  } in
  Lib.add_leaf (inTac2Notation ext);
  {
    nota_local = local;
    nota_raw = tkn;
    nota_depr = deprecation;
    nota_parsing = parsing;
    nota_tok = tokens;
    nota_body = body;
  }

let intern_notation_interpretation intern_body data =
  let accumulate_ids acc = function
    | TacTerm _ -> acc
    | TacNonTerm (Anonymous, _) -> acc
    | TacNonTerm (Name id, _) -> Id.Set.add id acc
  in
  let ids = List.fold_left accumulate_ids Id.Set.empty data.nota_tok in
  let body = intern_body ids data.nota_body in
  { data with nota_body = body }

let register_notation_interpretation data =
  Lib.add_leaf (inTac2NotationInterp data)

module Internal = struct
  let ltac2_expr = internal_ltac2_expr
end
