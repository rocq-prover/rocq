(************************************************************************)
(* Standalone plugin: a programmable [#[hint(...)]] attribute.          *)
(*                                                                      *)
(* Attaching                                                            *)
(*                                                                      *)
(*   #[hint(db=mydb, cost="2", visibility=export)]                      *)
(*                                                                      *)
(* to a [Definition], [Lemma], [Theorem], [Fixpoint], ... registers the *)
(* resulting constant in the hint database [mydb] as a [Resolve] hint   *)
(* with priority [2] and the given visibility, as soon as the           *)
(* declaration is completed (at [Qed]/[Defined] for proofs).  It is     *)
(* equivalent to running, immediately after the definition:             *)
(*                                                                      *)
(*   #[export] Hint Resolve name | 2 : mydb.                            *)
(*                                                                      *)
(* The keys are:                                                        *)
(*   - db          (required) the target hint database;                 *)
(*   - cost        (optional) the hint priority/cost, an integer given  *)
(*                 as a string literal (attribute values cannot be bare *)
(*                 numbers); omitted means the default priority;        *)
(*   - visibility  (optional) one of [local], [export] or [global];     *)
(*                 omitted behaves like a plain [Hint Resolve] (i.e.    *)
(*                 [local] inside a section, [export] otherwise).        *)
(************************************************************************)

open Attributes
open Attributes.Notations

(* The hint database name: [db=mydb] or [db="mydb"]. *)
let db_attr : string option attribute =
  let parser ?loc prev v =
    let () = match prev with
      | Some _ -> CErrors.user_err ?loc Pp.(str "Key \"db\" was already set.")
      | None -> ()
    in
    match v with
    | VernacFlagLeaf (FlagString s) -> s
    | VernacFlagLeaf (FlagQualid q) -> Libnames.string_of_qualid q
    | _ ->
      CErrors.user_err ?loc Pp.(str "Key \"db\" expects a value, e.g. db=mydb.")
  in
  attribute_of_list ["db", parser]

(* The hint cost / priority: [cost="2"].  Attribute values can only be string
   literals or qualified names, never bare numbers, so the integer is given as
   a string. *)
let cost_attr : int option attribute =
  let parser ?loc prev v =
    let () = match prev with
      | Some _ -> CErrors.user_err ?loc Pp.(str "Key \"cost\" was already set.")
      | None -> ()
    in
    let s = match v with
      | VernacFlagLeaf (FlagString s) -> s
      | VernacFlagLeaf (FlagQualid q) -> Libnames.string_of_qualid q
      | _ ->
        CErrors.user_err ?loc
          Pp.(str "Key \"cost\" expects a number, e.g. cost=\"2\".")
    in
    match int_of_string_opt s with
    | Some n -> n
    | None ->
      CErrors.user_err ?loc
        Pp.(str "Key \"cost\" expects an integer, got \"" ++ str s ++ str "\".")
  in
  attribute_of_list ["cost", parser]

(* The visibility: [visibility=local|export|global]. *)
let visibility_attr : Hints.hint_locality option attribute =
  key_value_attribute ~key:"visibility" ?empty:None
    ~values:[ "local",  Hints.Local
            ; "export", Hints.Export
            ; "global", Hints.SuperGlobal ]

type cfg = { db : string; cost : int option; vis : Hints.hint_locality option }

(* Parse the arguments of [hint(...)] into a [cfg]. *)
let parse_hint_args ?loc v =
  let inner = match v with
    | VernacFlagList l -> l
    | _ ->
      CErrors.user_err ?loc
        Pp.(str "The \"hint\" attribute expects arguments, e.g. \
                 #[hint(db=mydb, cost=\"1\", visibility=export)].")
  in
  let ((db, cost), vis) =
    Attributes.parse (db_attr ++ cost_attr ++ visibility_attr) inner
  in
  match db with
  | None ->
    CErrors.user_err ?loc
      Pp.(str "The \"hint\" attribute requires a \"db\" key, e.g. \
               #[hint(db=mydb)].")
  | Some db -> { db; cost; vis }

(* The completion hook: equivalent to [#[visibility] Hint Resolve name | cost : db]. *)
let resolve_hook { db; cost; vis } =
  Declare.Hook.make (fun { Declare.Hook.S.dref; _ } ->
      let locality = match vis with
        | Some l -> l
        | None ->
          if Lib.sections_are_opened () then Hints.Local else Hints.Export
      in
      let info = { Hints.empty_hint_info with Typeclasses.hint_priority = cost } in
      (* [true] is the [hnf] flag, matching the [Hint Resolve] vernacular. *)
      let entry = Hints.HintsResolveEntry [ (info, true, dref) ] in
      Hints.add_hints ~locality [db] entry)

let hint_attribute : Declare.Hook.t list Attributes.attribute =
  let parser ?loc _prev v = parse_hint_args ?loc v in
  map (function None -> [] | Some cfg -> [resolve_hook cfg])
    (attribute_of_list ["hint", parser])

(* Register and activate the observer when the plugin is loaded (i.e. on
   [Declare ML Module "rocq-hint-attr.hint"], directly or transitively via
   [Require Import HintAttr.HintAttr]).  Loading happens once per process, so a
   plain activation keeps the [#[hint(...)]] attribute available for the rest
   of the session. *)
let hint_token =
  Vernacentries.DefAttributes.Observer.register
    ~name:"hint-resolve-attribute" hint_attribute

let () = Vernacentries.DefAttributes.Observer.activate hint_token
