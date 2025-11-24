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
open Names

type is_type = bool (* Module Type or just Module *)
type export_flag = Export | Import
type export = (export_flag * Libobject.open_filter) option (* None for a Module Type *)

let make_oname Libobject.{ obj_path; obj_mp } id =
  Names.(Libnames.add_path_suffix obj_path id, KerName.make obj_mp id)

type 'summary node =
  | CompilingLibrary of Libobject.object_prefix
  | OpenedModule of is_type * export * Libobject.object_prefix * 'summary
  | OpenedSection of Libobject.object_prefix * 'summary

let node_prefix = function
  | CompilingLibrary prefix
  | OpenedModule (_,_,prefix,_)
  | OpenedSection (prefix,_) -> prefix

let prefix_id prefix = Libnames.basename prefix.Libobject.obj_path

type 'summary library_segment = ('summary node * Libobject.t list) list

let module_kind is_type =
  if is_type then "module type" else "module"

type classified_objects = {
  substobjs : Libobject.t list;
  keepobjs : Libobject.keep_objects;
  escapeobjs : Libobject.escape_objects;
  anticipateobjs : Libobject.t list;
}

let empty_classified = {
  substobjs = [];
  keepobjs = { keep_objects = [] };
  escapeobjs = { escape_objects = [] };
  anticipateobjs = [];
}

let classify_object classify_atom : Libobject.t -> Libobject.substitutivity = function
  | ModuleObject _ | ModuleTypeObject _ | IncludeObject _ | ExportObject _ -> Substitute
  | KeepObject _ -> Keep
  | EscapeObject _ -> Escape
  | AtomicObject o -> classify_atom o

let classify_segment classify_atom seg =
  let rec clean acc = function
    | [] -> acc
    | o :: stk ->
      begin match classify_object classify_atom o with
      | Dispose -> clean acc stk
      | Substitute ->
        clean {acc with substobjs = o :: acc.substobjs} stk
      | Keep ->
        clean {acc with keepobjs = { keep_objects = o :: acc.keepobjs.keep_objects } } stk
      | Escape ->
        clean {acc with escapeobjs = { escape_objects = o :: acc.escapeobjs.escape_objects } } stk
      | Anticipate ->
        clean {acc with anticipateobjs = o :: acc.anticipateobjs} stk
      end
  in
  clean empty_classified (List.rev seg)

let find_entries_p p stk =
  let rec find = function
    | [] -> []
    | (ent,_)::l -> if p ent then ent::find l else find l
  in
  find stk

let split_lib_at_opening stk =
  match stk with
  | [] -> assert false
  | (node,leaves) :: rest -> List.rev leaves, node, rest

let is_opening_node = function
  | OpenedSection _ | OpenedModule _ -> true
  | CompilingLibrary _ -> false

let open_blocks_message es =
  let open Pp in
  let open_block_name = function
    | OpenedSection (prefix,_) ->
      str "section " ++ Id.print (prefix_id prefix)
    | OpenedModule (ty,_,prefix,_) ->
      str (module_kind ty) ++ spc () ++ Id.print (prefix_id prefix)
    | _ -> assert false
  in
  str "The " ++ pr_enum open_block_name es ++ spc () ++
  str "need" ++ str (if List.length es == 1 then "s" else "") ++
  str " to be closed."

(* We keep trace of operations in the stack [lib_stk].
   [path_prefix] is the current path of sections, where sections are stored in
   ``correct'' order, the oldest coming first in the list. It may seems
   costly, but in practice there is not so many openings and closings of
   sections, but on the contrary there are many constructions of section
   paths based on the library path. *)

let dummy_prefix = Libobject.{
  obj_path = Libnames.dummy_full_path;
  obj_mp  = ModPath.dummy;
}

type synterp_state = {
  comp_name : DirPath.t option;
  lib_stk : Summary.Synterp.frozen library_segment;
  path_prefix : Libobject.object_prefix;
}

let dummy = {
  comp_name = None;
  lib_stk = [];
  path_prefix = dummy_prefix;
}

(** The lib state is split in two components:
  - The synterp stage state which manages a recording of syntax-related objects and naming-related data (compilation unit name, current prefix).
  - The interp stage state which manages a recording of regular objects.
*)

let synterp_state = ref dummy
let interp_state = ref ([] : Summary.Interp.frozen library_segment)

let library_info = ref UserWarn.empty

let contents () = !interp_state

let start_compilation s mp =
  if !synterp_state.comp_name != None then
    CErrors.user_err Pp.(str "compilation unit is already started");
  assert (List.is_empty !synterp_state.lib_stk);
  assert (List.is_empty !interp_state);
  let path = try
      let prefix, id = Libnames.split_dirpath s in
      Libnames.make_path prefix id
    with Failure _ -> CErrors.anomaly Pp.(str "Cannot start compilation with empty dirpath")
  in
  let prefix = Libobject.{ obj_path = path; obj_mp = mp } in
  let initial_stk = [ CompilingLibrary prefix, [] ] in
  let st = {
    comp_name = Some s;
    path_prefix = prefix;
    lib_stk = initial_stk;
  }
  in
  synterp_state := st;
  interp_state := initial_stk;
  Nametab.OpenMods.push (Until 1) path (DirOpenModule mp)

let end_compilation_checks dir =
  let () = match find_entries_p is_opening_node !interp_state with
    | [] -> ()
    | es -> CErrors.user_err (open_blocks_message es) in
  let () =
    match !synterp_state.comp_name with
      | None -> CErrors.anomaly (Pp.str "There should be a module name...")
      | Some m ->
          if not (Names.DirPath.equal m dir) then
            CErrors.anomaly Pp.(str "The current open module has name"
              ++ spc () ++ DirPath.print m ++ spc () ++ str "and not"
              ++ spc () ++ DirPath.print dir ++ str ".");
  in
  ()

let library_dp () =
  match !synterp_state.comp_name with Some m -> m | None -> DirPath.dummy

(* [path_prefix] is a pair of absolute dirpath and a pair of current
   module path and relative section path *)

let prefix () = !synterp_state.path_prefix
let cwd () = !synterp_state.path_prefix.Libobject.obj_path
let current_mp () = !synterp_state.path_prefix.Libobject.obj_mp

let sections_depth () =
  !synterp_state.lib_stk |> List.count (function
      | (OpenedSection _, _) -> true
      | ((OpenedModule _ | CompilingLibrary _), _) -> false)

let sections_are_opened () =
  match split_lib_at_opening !synterp_state.lib_stk with
  | (_, OpenedSection _, _) -> true
  | _ -> false

let cwd_except_section () =
  Libnames.path_pop_n_suffixes (sections_depth ()) (cwd ())

let current_dirpath sec =
  Libnames.drop_dirpath_prefix (library_dp ())
    (Libnames.dirpath_of_path (if sec then cwd () else cwd_except_section ()))

let make_path id = Libnames.add_path_suffix (cwd ()) id

let make_path_except_section id =
  Libnames.add_path_suffix (cwd_except_section ()) id

let make_kn id =
  let mp = current_mp () in
  Names.KerName.make mp id

let make_foname id = make_oname !synterp_state.path_prefix id

(* Adding operations. *)

let dummylib = CompilingLibrary dummy_prefix

let error_still_opened s oname =
  CErrors.user_err Pp.(str "The " ++ str s ++ str " "
    ++ Id.print (prefix_id oname) ++ str " is still opened.")

let recalc_path_prefix () =
  let path_prefix = match pi2 (split_lib_at_opening !synterp_state.lib_stk) with
    | CompilingLibrary dir
    | OpenedModule (_, _, dir, _)
    | OpenedSection (dir, _) -> dir
  in
  synterp_state := { !synterp_state with path_prefix }

let pop_path_prefix () =
  let op = !synterp_state.path_prefix in
  synterp_state := {
    !synterp_state
    with path_prefix = Libobject.{
        op with obj_path = Libnames.path_pop_suffix op.obj_path;
      } }

(* Modules. *)

(* Returns true if we are inside an opened module or module type *)
let is_module_or_modtype () =
  let rec aux = function
    | [] -> assert false
    | (OpenedSection _, _) :: rest -> aux rest
    | (OpenedModule _, _) :: _ -> true
    | (CompilingLibrary _, _) :: _ -> false
  in
  aux (!synterp_state).lib_stk

let is_modtype () =
  List.exists (function OpenedModule (istyp, _, _, _), _ -> istyp | _ -> false)
    (!synterp_state).lib_stk

let is_modtype_strict () =
  let rec aux = function
    | [] -> assert false
    | (OpenedSection _, _) :: rest -> aux rest
    | (OpenedModule (istyp, _, _, _), _) :: _ -> istyp
    | (CompilingLibrary _, _) :: _ -> false
  in
  aux (!synterp_state).lib_stk

let is_module () =
  List.exists (function OpenedModule (istyp, _, _, _), _ -> not istyp | _ -> false)
    (!synterp_state).lib_stk

(* Misc *)

type 'obj discharged_item =
  | DischargedExport of Libobject.ExportObj.t
  | DischargedLeaf of 'obj

let mp_of_global = let open GlobRef in function
  | VarRef id -> !synterp_state.path_prefix.Libobject.obj_mp
  | ConstRef cst -> Names.Constant.modpath cst
  | IndRef ind -> Names.Ind.modpath ind
  | ConstructRef constr -> Names.Construct.modpath constr

let rec split_modpath = function
  |Names.MPfile dp -> dp, []
  |Names.MPbound mbid -> library_dp (), [Names.MBId.to_id mbid]
  |Names.MPdot (mp,l) ->
    let (dp,ids) = split_modpath mp in
    (dp, l :: ids)

let library_part = function
  | GlobRef.VarRef id -> library_dp ()
  | ref -> ModPath.dp (mp_of_global ref)

let debug_object_name = function
  | Libobject.ModuleObject _ -> "ModuleObject"
  | ModuleTypeObject  _-> "ModuleTypeObject"
  | IncludeObject _ -> "IncludeObject"
  | KeepObject _ -> "KeepObject"
  | EscapeObject _ -> "EscapeObject"
  | ExportObject _ -> "ExportObject"
  | AtomicObject (Dyn (tag,_)) -> Libobject.Dyn.repr tag

let anomaly_unitialized_add_leaf stage o =
  CErrors.anomaly
    Pp.(str "cannot add object (" ++ str (debug_object_name o) ++ pr_comma() ++
        str "in " ++ str stage ++ str "): not initialized")

(** The [LibActions] abstraction represent the set of operations on the Lib
    structure that is specific to a given stage. Two instances are defined below,
    for Synterp and Interp. *)
module type LibActions = sig

  type summary
  type summary_mut
  type frozen_summary

  val stage : Summary.Stage.t

  val get_summary : summary_mut -> summary

  val open_section : summary -> Id.t -> unit

  val close_section : summary_mut -> frozen_summary -> unit

  val add_entry : frozen_summary node -> unit
  val add_leaf_entry : Libobject.t -> unit
  val start_mod : is_type:is_type -> export -> Id.t -> ModPath.t -> frozen_summary -> Libobject.object_prefix

  val get_lib_stk : unit -> frozen_summary library_segment
  val set_lib_stk : frozen_summary library_segment -> unit

  val pop_path_prefix : unit -> unit
  val recalc_path_prefix : unit -> unit

  type frozen
  val freeze : unit -> frozen
  val unfreeze : frozen -> unit
  val init : unit -> unit

  val drop_objects : frozen -> frozen

  val declare_info : Library_info.t -> unit

end

module SynterpActions = struct

  type summary = Summary.Synterp.t
  type summary_mut = Summary.Synterp.mut
  type frozen_summary = Summary.Synterp.frozen

  let stage = Summary.Stage.Synterp

  let get_summary = Summary.Synterp.get

  let check_section_fresh obj_path id =
    if Nametab.exists_dir obj_path then
      CErrors.user_err Pp.(Id.print id ++ str " already exists.")

  let push_section_name obj_path =
    Nametab.(push_dir (Until 1) obj_path (GlobDirRef.DirOpenSection obj_path))

  let close_section summary fs =
    Summary.Synterp.unfreeze_summaries fs summary

  let add_entry node =
    synterp_state := { !synterp_state with lib_stk = (node,[]) :: !synterp_state.lib_stk }

  let add_leaf_entry leaf =
    let lib_stk = match !synterp_state.lib_stk with
      | [] ->
        (* top_printers does set_bool_option_value which adds a leaf *)
        if !Flags.in_debugger then [dummylib, [leaf]] else anomaly_unitialized_add_leaf "synterp" leaf
      | (node, leaves) :: rest -> (node, leaf :: leaves) :: rest
    in
    synterp_state := { !synterp_state with lib_stk }

  (* Returns the opening node of a given name *)
  let start_mod ~is_type export id mp fs =
    let dir = Libnames.add_path_suffix !synterp_state.path_prefix.Libobject.obj_path id in
    let prefix = Libobject.{ obj_path = dir; obj_mp = mp; } in
    assert (not (sections_are_opened()));
    add_entry (OpenedModule (is_type,export,prefix,fs));
    synterp_state := { !synterp_state with path_prefix = prefix } ;
    prefix

  let get_lib_stk () =
    !synterp_state.lib_stk

  let set_lib_stk stk =
    synterp_state := { !synterp_state with lib_stk = stk }

  let open_section summary id =
    let opp = !synterp_state.path_prefix in
    let obj_path = Libnames.add_path_suffix opp.Libobject.obj_path id in
    let prefix = Libobject.{ obj_path; obj_mp=opp.obj_mp; } in
    check_section_fresh obj_path id;
    let fs = Summary.Synterp.freeze_summaries summary in
    add_entry (OpenedSection (prefix, fs));
    (*Pushed for the lifetime of the section: removed by unfreezing the summary*)
    push_section_name obj_path;
    synterp_state := { !synterp_state with path_prefix = prefix }

  let pop_path_prefix () = pop_path_prefix ()
  let recalc_path_prefix () = recalc_path_prefix ()

  type frozen = synterp_state

  let freeze () = !synterp_state

  let unfreeze st =
    synterp_state := st

  let init () =
    synterp_state := dummy

  let drop_objects st =
    let drop_node = function
      | CompilingLibrary _ as x -> x
      | OpenedModule (it,e,op,_) ->
        OpenedModule(it,e,op,Summary.Synterp.empty_frozen)
      | OpenedSection (op, _) ->
        OpenedSection(op,Summary.Synterp.empty_frozen)
    in
    let lib_synterp_stk = List.map (fun (node,_) -> drop_node node, []) st.lib_stk in
    { st with lib_stk = lib_synterp_stk }

  let declare_info info =
    let open UserWarn in
    let depr = match !library_info.depr, info.depr with
      | None, depr | depr, None -> depr
      | Some _, Some _ ->
         CErrors.user_err Pp.(str "Library file is already deprecated.") in
    let warn = !library_info.warn @ info.warn in
    library_info := { depr; warn }

end

module InterpActions = struct

  type summary = Summary.Interp.t
  type summary_mut = Summary.Interp.mut
  type frozen_summary = Summary.Interp.frozen

  let stage = Summary.Stage.Interp

  let get_summary = Summary.Interp.get

  let close_section summary fs = Global.close_section summary fs

  let add_entry node =
    interp_state := (node,[]) :: !interp_state

  let add_leaf_entry leaf =
    let lib_stk = match !interp_state with
      | [] ->
        (* top_printers does set_bool_option_value which adds a leaf *)
        if !Flags.in_debugger then [dummylib, [leaf]] else anomaly_unitialized_add_leaf "interp" leaf
      | (node, leaves) :: rest -> (node, leaf :: leaves) :: rest
    in
    interp_state := lib_stk

  (* Returns the opening node of a given name *)
  let start_mod ~is_type export id mp fs =
    let prefix = !synterp_state.path_prefix in
    add_entry (OpenedModule (is_type,export,prefix,fs));
    prefix

  let get_lib_stk () =
    !interp_state

  let set_lib_stk stk =
    interp_state := stk

  let open_section summary id =
    Global.open_section ();
    let prefix = !synterp_state.path_prefix in
    let fs = Summary.Interp.freeze_summaries summary in
    add_entry (OpenedSection (prefix, fs))

  let pop_path_prefix () = ()
  let recalc_path_prefix () = ()

  type frozen = frozen_summary library_segment

  let freeze () = !interp_state

  let unfreeze st =
    interp_state := st

  let init () =
    interp_state := []

  let drop_objects interp_state =
    let drop_node = function
      | CompilingLibrary _ as x -> x
      | OpenedModule (it,e,op,_) ->
        OpenedModule(it,e,op,Summary.Interp.empty_frozen)
      | OpenedSection (op, _) ->
        OpenedSection(op,Summary.Interp.empty_frozen)
    in
    List.map (fun (node,_) -> drop_node node, []) interp_state

  let declare_info _ = ()

end

module type StagedLibS = sig

  type summary
  type summary_mut
  type frozen_summary
  type discharged_obj

  (** {6 ... } *)
  (** Adding operations (which call the [cache] method, and getting the
      current list of operations (most recent ones coming first). *)

  val add_leaf : summary_mut -> Libobject.obj -> unit

  val add_discharged_leaf : summary_mut -> discharged_obj -> unit

  (** Returns the opening node of a given name *)
  val find_opening_node : ?loc:Loc.t -> Id.t -> frozen_summary node

  val add_entry : frozen_summary node -> unit
  val add_leaf_entry : Libobject.t -> unit

  (** {6 Sections } *)
  val open_section : summary -> Id.t -> unit

  (** [close_section] needs to redo Export, so the complete
      implementation needs to involve [Declaremods]. *)
  val close_section : summary_mut -> discharged_obj discharged_item list

  (** {6 Modules and module types } *)

  val start_module :
    export -> Id.t -> ModPath.t ->
    frozen_summary -> Libobject.object_prefix

  val start_modtype :
    Id.t -> ModPath.t ->
    frozen_summary -> Libobject.object_prefix

  val end_module :
    unit ->
    Libobject.object_prefix * frozen_summary * classified_objects

  val end_modtype :
    unit ->
    Libobject.object_prefix * frozen_summary * classified_objects

  type frozen

  val freeze : unit -> frozen
  val unfreeze : frozen -> unit
  val init : unit -> unit

  (** Keep only the libobject structure, not the objects themselves *)
  val drop_objects : frozen -> frozen

  val declare_info : Library_info.t -> unit

end

(** The [StagedLib] abstraction factors out the code dealing with Lib structure
    that is common to all stages. *)
module StagedLib
    (Actions : LibActions)
    (OStage:Libobject.Staged
     with type summary = Actions.summary
      and type summary_mut = Actions.summary_mut)
  : StagedLibS
    with type summary = Actions.summary
     and type summary_mut = Actions.summary_mut
     and type frozen_summary = Actions.frozen_summary = struct

  type summary = Actions.summary
  type summary_mut = Actions.summary_mut
  type frozen_summary = Actions.frozen_summary
  type discharged_obj = OStage.discharged_obj

  let add_discharged_leaf sum obj =
    let newobj = OStage.rebuild_object (Actions.get_summary sum) obj in
    OStage.cache_object (prefix(),newobj) sum;
    Actions.add_leaf_entry (AtomicObject newobj)

  let add_leaf sum obj =
    OStage.cache_object (prefix(),obj) sum;
    let ostage = Actions.stage in
    let ok_stage = match !Flags.in_synterp_phase with
      | None -> true
      | Some false -> ostage == Interp
      | Some true -> ostage == Synterp
    in
    let () = if not ok_stage then
        let ppstage = match ostage with Interp -> "interp" | Synterp -> "synterp" in
        CErrors.anomaly
          Pp.(str "Adding object " ++
              str (OStage.object_name obj) ++
              str " in incorrect stage (object_stage = " ++ str ppstage ++ str ").")
    in
    Actions.add_leaf_entry (AtomicObject obj)

  let add_entry node = Actions.add_entry node
  let add_leaf_entry obj = Actions.add_leaf_entry obj

  let open_section = Actions.open_section

  exception WrongClosingBlockName of Id.t * Loc.t option

  let () = CErrors.register_handler (function
      | WrongClosingBlockName (id,_) ->
        Some Pp.(str "Last block to end has name " ++ Id.print id ++ str ".")
      | _ -> None)

  let () = Quickfix.register (function
      | WrongClosingBlockName (id, Some loc) -> [Quickfix.make ~loc (Id.print id)]
      | _ -> [])

  let find_opening_node ?loc id =
    let entry = match Actions.get_lib_stk () with
      | [] -> assert false
      | (CompilingLibrary _, _) :: _ ->
        CErrors.user_err Pp.(str "There is nothing to end.")
      | (entry, _) :: _ -> entry
    in
    let id' = prefix_id (node_prefix entry) in
    if not (Names.Id.equal id id') then
      Loc.raise ?loc (WrongClosingBlockName(id',loc));
    entry

  let start_module = Actions.start_mod ~is_type:false
  let start_modtype = Actions.start_mod ~is_type:true None

  let end_mod ~is_type =
    let (after,mark,before) = split_lib_at_opening (Actions.get_lib_stk ()) in
    (* The errors here should not happen because we checked in the upper layers *)
    let prefix, fs = match mark with
      | OpenedModule (ty,_,prefix,fs) ->
        if ty == is_type then prefix, fs
        else error_still_opened (module_kind ty) prefix
      | OpenedSection (prefix, _) -> error_still_opened "section" prefix
      | CompilingLibrary _ -> CErrors.user_err (Pp.str "No opened modules.")
    in
    Actions.set_lib_stk before;
    Actions.recalc_path_prefix ();
    let after = classify_segment OStage.classify_object after in
    (prefix, fs, after)

  let end_module () = end_mod ~is_type:false
  let end_modtype () = end_mod ~is_type:true

  let discharge_item sum = function
    | Libobject.ModuleObject _ | ModuleTypeObject _ | IncludeObject _ | KeepObject _ | EscapeObject _ ->
      assert false
    | ExportObject o -> Some (DischargedExport o)
    | AtomicObject obj ->
      let obj = OStage.discharge_object sum obj in
      Option.map (fun o -> DischargedLeaf o) obj

  (* Restore lib_stk and summaries as before the section opening, and
     add a ClosedSection object. *)
  let close_section summary =
    let (secdecls,mark,before) = split_lib_at_opening (Actions.get_lib_stk ()) in
    let fs = match mark with
      | OpenedSection (_,fs) -> fs
      | _ -> CErrors.user_err Pp.(str "No opened section.")
    in
    Actions.set_lib_stk before;
    Actions.pop_path_prefix ();
    let newdecls = List.filter_map (discharge_item (Actions.get_summary summary)) secdecls in
    Actions.close_section summary fs;
    newdecls

  type frozen = Actions.frozen

  let freeze () = Actions.freeze ()

  let unfreeze st = Actions.unfreeze st

  let init () = Actions.init ()

  let drop_objects st = Actions.drop_objects st

  let declare_info info = Actions.declare_info info

end

module Synterp = StagedLib(SynterpActions)(Libobject.Synterp)
module Interp = StagedLib(InterpActions)(Libobject.Interp)

type compilation_result = {
  info : Library_info.t;
  synterp_objects : classified_objects;
  interp_objects : classified_objects;
}

let end_compilation dir =
  end_compilation_checks dir;
  let (syntax_after,_,syntax_before) = split_lib_at_opening !synterp_state.lib_stk in
  let (after,_,before) = split_lib_at_opening !interp_state in
  assert (List.is_empty syntax_before);
  assert (List.is_empty before);
  synterp_state := { !synterp_state with comp_name = None };
  let syntax_after = classify_segment Libobject.Synterp.classify_object syntax_after in
  let after = classify_segment Libobject.Interp.classify_object after in
  { info = !library_info; interp_objects = after; synterp_objects = syntax_after; }

(** Compatibility layer *)
let init () =
  Synterp.init ();
  Interp.init ()
