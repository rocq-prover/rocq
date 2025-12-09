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
open Genarg
open Gramlib

module Syn = struct
  type t = Summary.Synterp.t
end

(** The parser of Rocq *)
module Functional = Grammar.GMake(Syn)(CLexer.Lexer)
include Functional

let add_kw = { add_kw = CLexer.add_keyword_tok }

let no_add_kw = { add_kw = fun () _ -> () }

let extend_gstate ~ignore_kw estate kwstate e ext =
  let estate, kwstate =
    if ignore_kw then
      let estate, () = safe_extend no_add_kw estate () e ext in
      estate, kwstate
    else safe_extend add_kw estate kwstate e ext
  in
  estate, kwstate

(** Unsynchronized grammar extensions *)

type unsync_ext =
| UGramExt : { ignore_kw:bool; entry : 'a Entry.t; ext : 'a extend_statement } -> unsync_ext
| UEntryExt : 'a Entry.t * 'a Entry.parser_fun option -> unsync_ext

(** int is the length of the list *)
let unsync_state : (int * unsync_ext list * EState.t * CLexer.keyword_state) ref =
  ref (0, [], EState.empty, CLexer.empty_keyword_state)

let grammar_extend ~ignore_kw e ext =
  let ulen, exts, estate, kwstate = !unsync_state in
  let estate, kwstate = extend_gstate ~ignore_kw estate kwstate e ext in
  unsync_state := (ulen+1, UGramExt {ignore_kw; entry=e; ext} :: exts, estate, kwstate)

let entry_extend_unsync name parser_opt =
  let ulen, exts, estate, kwstate = !unsync_state in
  let estate, entry = match parser_opt with
    | None -> Entry.make name estate
    | Some p -> Entry.of_parser name p estate
  in
  unsync_state := (ulen+1, UEntryExt (entry, parser_opt) :: exts, estate, kwstate);
  entry

let replay_extend_entry entry parser_opt estate =
  match parser_opt with
  | None -> Unsafe.existing_entry estate entry
  | Some p -> Unsafe.existing_of_parser estate entry p

let replay_one_unsync_extend ext (estate,kwstate) =
  match ext with
  | UGramExt {ignore_kw; entry; ext} -> extend_gstate ~ignore_kw estate kwstate entry ext
  | UEntryExt (e,p) -> replay_extend_entry e p estate, kwstate

let replay_unsync_extends exts gstate =
  List.fold_right replay_one_unsync_extend exts gstate

(** Marshallable representation of grammar extensions *)

module EntryCommand = Dyn.Make ()
module GrammarCommand = Dyn.Make ()
module GramState = Store.Make ()

type gramext = { ignore_kw:bool; entry:GrammarCommand.t }

type grammar_entry =
| GramExt of gramext
| EntryExt : ('a * 'b) EntryCommand.tag * 'a -> grammar_entry
| KeywordExt of string list

let make_gstate sum estate kwstate = {
  GState.estate;
  kwstate;
  recover = true;
  has_non_assoc = false;
  synstate = sum;
}

(** State handling (non marshallable!) *)

module FullState = struct
  type t = {
    (* the state used for parsing *)
    current_state : EState.t;
    current_kws : CLexer.keyword_state;
    (* Number of unsynchronized extensions added to current_state *)
    unsync_exts : int;
    (* when all unsynchronized extensions have been added,
       current_state = List.fold_right add_entry current_sync_extensions (pi3 !unsync_state)
       this means the list is in reverse order of addition *)
    current_sync_extensions : grammar_entry list;
    (* some user data tied to the grammar state, typically contains info on declared levels
       and maps custom entry names to the actual Entry.t values *)
    user_state : GramState.t;
  }

  let empty =
    {
      current_state = EState.empty;
      current_kws = CLexer.empty_keyword_state;
      unsync_exts = 0;
      current_sync_extensions = [];
      user_state = GramState.empty;
    }

  let gramstate s = s.user_state

  let kwstate s = s.current_kws

  let estate s = s.current_state

  let gstate sum s = make_gstate sum s.current_state s.current_kws

  let from_unsync_state () =
    let ulen, _, estate, kwstate = !unsync_state in
    {
      current_state = estate;
      current_kws = kwstate;
      unsync_exts = ulen;
      current_sync_extensions = [];
      user_state = GramState.empty;
    }
end
open FullState

(** Summary functions: the state of the lexer is included in that of the parser.
   Because the grammar affects the set of keywords when adding or removing
   grammar rules. *)
type frozen_t = {
  frozen_sync : grammar_entry list;
}

(** Synchronized grammar extensions *)

type extend_rule =
| ExtendRule : 'a Entry.t * 'a extend_statement -> extend_rule

type 'a grammar_extension = {
  gext_fun : 'a -> FullState.t -> extend_rule list * GramState.t;
  gext_eq : 'a -> 'a -> bool;
}

module GrammarInterp = struct type 'a t = 'a grammar_extension end
module GrammarInterpMap = GrammarCommand.Map(GrammarInterp)

let grammar_interp = ref GrammarInterpMap.empty

type 'a grammar_command = 'a GrammarCommand.tag

let create_grammar_command name interp : _ grammar_command =
  let obj = GrammarCommand.create name in
  let () = grammar_interp := GrammarInterpMap.add obj interp !grammar_interp in
  obj

let grammar_extend_sync ~ignore_kw user_state entry rules state =
  let extend_one_sync (estate,kwstate) = function
    | ExtendRule (e, ext) -> extend_gstate estate kwstate e ext
  in
  let current_state,current_kws =
    List.fold_left (extend_one_sync ~ignore_kw) (state.current_state,state.current_kws) rules
  in
  { state with
    current_state;
    current_kws;
    user_state;
    current_sync_extensions = GramExt {ignore_kw; entry} :: state.current_sync_extensions;
  }

let extend_grammar_command ~ignore_kw tag g state =
  let modify = GrammarInterpMap.find tag !grammar_interp in
  let (rules, st) = modify.gext_fun g state in
  grammar_extend_sync ~ignore_kw st (Dyn (tag,g)) rules state

type ('a,'b) entry_extension = {
  eext_fun : 'a -> 'b Entry.t -> FullState.t -> GramState.t;
  eext_name : 'a -> string;
  eext_eq : 'a -> 'a -> bool;
}

let extend_entry_sync (type a b)
    (tag : (a * b) EntryCommand.tag)
    (interp:(a,b) entry_extension)
    (data:a)
    state
  =
  let name = interp.eext_name data in
  let current_estate, e = Entry.make name state.current_state in
  let user_state = interp.eext_fun data e state in
  let state = {
    state with
    current_state = current_estate;
    current_sync_extensions = EntryExt (tag,data) :: state.current_sync_extensions;
    user_state;
  }
  in
  state

module EntryInterp = struct type _ t = EExt : ('a,'b) entry_extension -> ('a * 'b) t end
module EntryInterpMap = EntryCommand.Map(EntryInterp)

let entry_interp = ref EntryInterpMap.empty

type ('a,'b) entry_command = ('a * 'b) EntryCommand.tag

let create_entry_command name interp : _ entry_command =
  let obj = EntryCommand.create name in
  let () = entry_interp := EntryInterpMap.add obj (EExt interp) !entry_interp in
  obj

let extend_entry_command tag data state =
  let EExt interp = EntryInterpMap.find tag !entry_interp in
  extend_entry_sync tag interp data state

let extend_keywords kws state = {
  state with
  current_kws = List.fold_left CLexer.add_keyword state.current_kws kws;
  current_sync_extensions = KeywordExt kws :: state.current_sync_extensions;
}

(** Registering extra grammar *)

let grammar_names : Entry.any_t list String.Map.t ref = ref String.Map.empty

let register_grammars_by_name name grams =
  grammar_names := String.Map.add name grams !grammar_names

let find_grammars_by_name name =
  (* XXX look through custom entries somehow? *)
  Option.default [] (String.Map.find_opt name !grammar_names)

let eq_grams g1 g2 = match g1, g2 with
  | GramExt {ignore_kw=kw1;entry=GrammarCommand.Dyn (t1, v1)},
    GramExt {ignore_kw=kw2;entry=GrammarCommand.Dyn (t2, v2)} ->
  begin Bool.equal kw1 kw2 && match GrammarCommand.eq t1 t2 with
  | None -> false
  | Some Refl ->
    let data = GrammarInterpMap.find t1 !grammar_interp in
    data.gext_eq v1 v2
  end
| EntryExt (t1, d1), EntryExt (t2, d2) ->
  begin match EntryCommand.eq t1 t2 with
  | None -> false
  | Some Refl ->
    let EExt interp = EntryInterpMap.find t1 !entry_interp in
    interp.eext_eq d1 d2
  end
| KeywordExt l1, KeywordExt l2 -> l1 == l2 || List.equal String.equal l1 l2
| GramExt _, _ | EntryExt _, _ | KeywordExt _, _ -> false

(* We compare the current state of the grammar and the state to unfreeze,
   by computing the longest common suffixes *)
let factorize_grams l1 l2 =
  if l1 == l2 then ([], [], l1) else List.share_tails eq_grams l1 l2

let replay_sync_extension state = function
  | GramExt {ignore_kw;entry=Dyn(tag,g)} -> extend_grammar_command ~ignore_kw tag g state
  | EntryExt (tag,data) -> extend_entry_command tag data state
  | KeywordExt kws -> extend_keywords kws state

let replay_sync_extensions state to_add =
  List.fold_left replay_sync_extension state to_add

module UpdateState : sig
  type t
  val make : FullState.t -> t

  (** Returns the state with any new unsynchronized extensions included.
      Adding unsynchronized extensions is cached. *)
  val get : t -> FullState.t

  (** Does not need to update unsynchronized data *)
  val current_sync_extensions : t -> grammar_entry list

  val gramstate : t -> GramState.t
end = struct
  type t = FullState.t ref
  let make x = ref x

  let get state =
    let ulen, exts, _, _ = !unsync_state in
    if Int.equal ulen (!state).unsync_exts then !state
    else
      let exts = List.firstn (ulen - (!state).unsync_exts) exts in
      let estate, kwstate =
        replay_unsync_extends exts (!(state).current_state, (!state).current_kws)
      in
      let updated = {
        !state with
        current_state = estate;
        current_kws = kwstate;
        unsync_exts = ulen;
      }
      in
      let () = state := updated in
      updated

  let current_sync_extensions x = (!x).current_sync_extensions

  let gramstate x = (!x).user_state
end

let unfreeze (state, {frozen_sync}) =
  let state = Option.default (UpdateState.make FullState.empty) state in
  let to_remove, to_add, _common =
    factorize_grams (UpdateState.current_sync_extensions state) frozen_sync
  in
  if CList.is_empty to_remove then begin
    if CList.is_empty to_add then state
    else UpdateState.make @@ replay_sync_extensions (UpdateState.get state) (List.rev to_add)
  end
  else begin
    let state = from_unsync_state() in
    UpdateState.make @@ replay_sync_extensions state (List.rev frozen_sync);
  end

module GlobalState : sig

  val summary_tag : frozen_t Summary.Synterp.tag

  val gramstate : Summary.Synterp.t -> GramState.t

  val estate : Summary.Synterp.t -> EState.t

  val kwstate : Summary.Synterp.t -> CLexer.keyword_state

  val gstate : Summary.Synterp.t -> GState.t

  val modify_sync_state0 : Summary.Synterp.mut -> (FullState.t -> FullState.t) -> unit

  val freeze : Summary.Synterp.t -> frozen_t
  val unfreeze : Summary.Synterp.mut -> frozen_t -> unit

end = struct

  let state, summary_tag = Summary.Synterp.declare_tag_gen "GRAMMAR" {
      freeze = (fun state -> {frozen_sync = UpdateState.current_sync_extensions state});
      unfreeze;
      init = (fun () -> UpdateState.make FullState.empty);
    }

  (* no need to update, gramstate isn't modified by it *)
  let gramstate sum = UpdateState.gramstate (state.get sum)

  let estate sum =
    (UpdateState.get @@ state.get sum).current_state

  let kwstate sum =
    (UpdateState.get @@ state.get sum).current_kws

  let gstate sum =
    let state = UpdateState.get @@ state.get sum in
    FullState.gstate sum state

  let modify_sync_state sum f =
    let state', v = f (UpdateState.get @@ state.get (Summary.Synterp.get sum)) in
    let state' = UpdateState.make state' in
    state.set sum state';
    v

  let modify_sync_state0 sum f = modify_sync_state sum (fun state -> f state, ())

  let freeze sum = {
    frozen_sync = UpdateState.current_sync_extensions @@ state.get sum;
  }

  let unfreeze sum st =
    state.set sum @@ unfreeze (Some (state.get (Summary.Synterp.get sum)), st)

end
open GlobalState

let parser_summary_tag = summary_tag

let freeze = freeze
let unfreeze = unfreeze

let gramstate = gramstate

let gstate = gstate

let get_keyword_state = kwstate

let epsilon_value (type s tr a) sum f (e : (s, tr, a) Symbol.t) =
  let r = Production.make (Rule.next Rule.stop e) (fun x _ -> f x) in
  let estate = estate sum in
  let kwstate = kwstate sum in
  let estate, entry = Entry.make "epsilon" estate in
  let ext = Fresh (Gramlib.Gramext.First, [None, None, [r]]) in
  let estate, kwstate = safe_extend add_kw estate kwstate entry ext in
  let strm = Stream.empty () in
  let strm = Parsable.make strm in
  try Some (Entry.parse entry strm (make_gstate sum estate kwstate))
  with e when CErrors.noncritical e -> None

let extend_entry_command sum tag data =
  modify_sync_state0 sum (extend_entry_command tag data)

let extend_keywords sum kws =
  modify_sync_state0 sum (extend_keywords kws)

let extend_grammar_command sum ~ignore_kw tag g =
  modify_sync_state0 sum (extend_grammar_command ~ignore_kw tag g)

module Parsable = struct
  include Parsable
  let consume x len sum = consume x len (get_keyword_state sum)
end

module Entry = struct
  include Entry
  let make name = entry_extend_unsync name None
  let parse e p sum = parse e p (gstate sum)
  let of_parser na p = entry_extend_unsync na (Some p)
  let parse_token_stream e strm sum = parse_token_stream e strm (gstate sum)
  let print fmt e sum =  print fmt e (gstate sum)
  let is_empty e sum = is_empty e (gstate sum).estate
  let accumulate_in e sum = accumulate_in e (gstate sum).estate
  let all_in sum = all_in (gstate sum).estate
end

module Lookahead =
struct

  type t = int -> CLexer.keyword_state -> (CLexer.keyword_state,Tok.t) LStream.t -> int option

  let rec contiguous n m strm =
    n == m ||
    let (_, ep) = Loc.unloc (LStream.get_loc n strm) in
    let (bp, _) = Loc.unloc (LStream.get_loc (n + 1) strm) in
    Int.equal ep bp && contiguous (succ n) m strm

  let check_no_space m _kwstate strm =
    let n = LStream.count strm in
    if contiguous n (n+m-1) strm then Some m else None

  let to_entry s (lk : t) =
    let run gstate strm = match lk 0 gstate.GState.kwstate strm with
      | None -> Error ()
      | Some _ -> Ok ()
    in
    Entry.(of_parser s { parser_fun = run })

  let (>>) (lk1 : t) lk2 n kwstate strm = match lk1 n kwstate strm with
  | None -> None
  | Some n -> lk2 n kwstate strm

  let (<+>) (lk1 : t) lk2 n kwstate strm = match lk1 n kwstate strm with
  | None -> lk2 n kwstate strm
  | Some n -> Some n

  let lk_empty n kwstate strm = Some n

  let lk_kw kw n kwstate strm = match LStream.peek_nth kwstate n strm with
  | Some (Tok.KEYWORD kw' | Tok.IDENT kw') -> if String.equal kw kw' then Some (n + 1) else None
  | _ -> None

  let lk_kws kws n kwstate strm = match LStream.peek_nth kwstate n strm with
  | Some (Tok.KEYWORD kw | Tok.IDENT kw) -> if List.mem_f String.equal kw kws then Some (n + 1) else None
  | _ -> None

  let lk_ident n kwstate strm = match LStream.peek_nth kwstate n strm with
  | Some (Tok.IDENT _) -> Some (n + 1)
  | _ -> None

  let lk_name = lk_ident <+> lk_kw "_"

  let lk_ident_except idents n kwstate strm = match LStream.peek_nth kwstate n strm with
  | Some (Tok.IDENT ident) when not (List.mem_f String.equal ident idents) -> Some (n + 1)
  | _ -> None

  let lk_nat n kwstate strm = match LStream.peek_nth kwstate n strm with
  | Some (Tok.NUMBER p) when NumTok.Unsigned.is_nat p -> Some (n + 1)
  | _ -> None

  let rec lk_list lk_elem n kwstate strm =
    ((lk_elem >> lk_list lk_elem) <+> lk_empty) n kwstate strm

  let lk_ident_list = lk_list lk_ident

  let lk_field n kwstate strm = match LStream.peek_nth kwstate n strm with
    | Some (Tok.FIELD _) -> Some (n+1)
    | _ -> None

  let lk_qualid = lk_ident >> lk_list lk_field

end

(** An entry that checks we reached the end of the input. *)
(* used by the Tactician plugin *)
let eoi_entry en =
  let e = Entry.make ((Entry.name en) ^ "_eoi") in
  let symbs = Rule.next (Rule.next Rule.stop (Symbol.nterm en)) (Symbol.token Tok.PEOI) in
  let act = fun _ x loc -> x in
  let ext = Fresh (Gramlib.Gramext.First, [None, None, [Production.make symbs act]]) in
  (* ignore_kw: doesn't matter here, no potential keywords in the rule *)
  grammar_extend ~ignore_kw:true e ext;
  e

(* Parse a string, does NOT check if the entire string was read
   (use eoi_entry) *)

let parse_string sum f ?loc x =
  let strm = Stream.of_string x in
  Entry.parse f (Parsable.make ?loc strm) sum

module GrammarObj =
struct
  type ('r, _, _) obj = 'r Entry.t
  let name = "grammar"
  let default _ = None
end

module Grammar = Register(GrammarObj)

let register_grammar = Grammar.register0
let genarg_grammar x =
  Grammar.obj x

let create_generic_entry2 (type a) s (etyp : a raw_abstract_argument_type) : a Entry.t =
  let e = Entry.make s in
  let Rawwit t = etyp in
  let () = Grammar.register0 t e in
  e

(* Initial grammar entries *)
module Prim =
  struct

    (* Entries that can be referred via the string -> Entry.t table *)
    (* Typically for tactic or vernac extensions *)
    let preident = Entry.make "preident"
    let ident = Entry.make "ident"
    let natural = Entry.make "natural"
    let integer = Entry.make "integer"
    let bignat = Entry.make "bignat"
    let bigint = Entry.make "bigint"
    let string = Entry.make "string"
    let lstring = Entry.make "lstring"
    let reference = Entry.make "reference"
    let fields = Entry.make "fields"
    let by_notation = Entry.make "by_notation"
    let smart_global = Entry.make "smart_global"
    let strategy_level = Entry.make "strategy_level"

    (* parsed like ident but interpreted as a term *)
    let hyp = Entry.make "hyp"

    let name = Entry.make "name"
    let identref = Entry.make "identref"
    let univ_decl = Entry.make "univ_decl"
    let ident_decl = Entry.make "ident_decl"
    let pattern_ident = Entry.make "pattern_ident"

    let qualid = Entry.make "qualid"
    let fullyqualid = Entry.make "fullyqualid"
    let dirpath = Entry.make "dirpath"

    let ne_string = Entry.make "ne_string"
    let ne_lstring = Entry.make "ne_lstring"

    let bar_cbrace = Entry.make "'|}'"

  end

module Constr =
  struct

    (* Entries that can be referred via the string -> Entry.t table *)
    let constr = Entry.make "constr"
    let term = Entry.make "term"
    let constr_eoi = eoi_entry constr
    let lconstr = Entry.make "lconstr"
    let binder_constr = Entry.make "binder_constr"
    let ident = Entry.make "ident"
    let global = Entry.make "global"
    let universe_name = Entry.make "universe_name"
    let sort = Entry.make "sort"
    let sort_quality_or_set = Entry.make "sort_quality_or_set"
    let sort_quality_var = Entry.make "sort_quality_var"
    let pattern = Entry.make "pattern"
    let constr_pattern = Entry.make "constr_pattern"
    let cpattern = Entry.make "cpattern"
    let closed_binder = Entry.make "closed_binder"
    let binder = Entry.make "binder"
    let binders = Entry.make "binders"
    let open_binders = Entry.make "open_binders"
    let one_open_binder = Entry.make "one_open_binder"
    let one_closed_binder = Entry.make "one_closed_binder"
    let binders_fixannot = Entry.make "binders_fixannot"
    let typeclass_constraint = Entry.make "typeclass_constraint"
    let record_declaration = Entry.make "record_declaration"
    let arg = Entry.make "arg"
    let type_cstr = Entry.make "type_cstr"
  end

module Module =
  struct
    let module_expr = Entry.make "module_expr"
    let module_type = Entry.make "module_type"
  end

let with_grammar_rule_protection sum f =
  snd @@ Summary.Synterp.with_mut f sum

let unsync_keywords () =
  let _, _, _, kws = !unsync_state in
  kws
