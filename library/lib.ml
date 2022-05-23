(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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

let make_oname Nametab.{ obj_dir; obj_mp } id =
  Names.(Libnames.make_path obj_dir id, KerName.make obj_mp (Label.of_id id))

let oname_prefix (sp, kn) =
  { Nametab.obj_dir = Libnames.dirpath sp; obj_mp = KerName.modpath kn }

type node =
  | CompilingLibrary of Nametab.object_prefix
  | OpenedModule of is_type * export * Nametab.object_prefix * Summary.frozen
  | OpenedSection of Nametab.object_prefix * Summary.frozen

let node_prefix = function
  | CompilingLibrary prefix
  | OpenedModule (_,_,prefix,_)
  | OpenedSection (prefix,_) -> prefix

let prefix_id prefix = snd (Libnames.split_dirpath prefix.Nametab.obj_dir)

type library_segment = (node * Libobject.t list) list

type classified_objects = {
  substobjs : Libobject.t list;
  keepobjs : Libobject.t list;
  anticipateobjs : Libobject.t list;
}

let module_kind is_type =
  if is_type then "module type" else "module"

(*let load_and_subst_objects i prefix subst seg =
  List.rev (List.fold_left (fun seg (id,obj as node) ->
    let obj' =  subst_object (make_oname prefix id, subst, obj) in
    let node = if obj == obj' then node else (id, obj') in
    load_object i (make_oname prefix id, obj');
    node :: seg) [] seg)
*)
let classify_segment seg =
  let rec clean ((substl,keepl,anticipl) as acc) = function
    | [] -> acc
    | o :: stk ->
      let open Libobject in
      begin match o with
        | ModuleObject _ | ModuleTypeObject _ | IncludeObject _ ->
          clean (o::substl, keepl, anticipl) stk
        | KeepObject _ ->
          clean (substl, o::keepl, anticipl) stk
        | ExportObject _ ->
          clean (o::substl, keepl, anticipl) stk
        | AtomicObject obj as o ->
          begin match classify_object obj with
            | Dispose -> clean acc stk
            | Keep ->
              clean (substl, o::keepl, anticipl) stk
            | Substitute ->
              clean (o::substl, keepl, anticipl) stk
            | Anticipate ->
              clean (substl, keepl, o::anticipl) stk
          end
      end
  in
  clean ([],[],[]) (List.rev seg)

let classify_segment seg =
  let substobjs, keepobjs, anticipateobjs = classify_segment seg in
  { substobjs; keepobjs; anticipateobjs; }

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
  | _ -> false

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

module State = struct

(* We keep trace of operations in the stack [lib_stk].
   [path_prefix] is the current path of sections, where sections are stored in
   ``correct'' order, the oldest coming first in the list. It may seems
   costly, but in practice there is not so many openings and closings of
   sections, but on the contrary there are many constructions of section
   paths based on the library path. *)
type t = {
  lib_stk : library_segment;
  path_prefix : Nametab.object_prefix;
}
(* [path_prefix] is a pair of absolute dirpath and a pair of current
   module path and relative section path *)

let initial_prefix = Nametab.{
  obj_dir = Libnames.default_library;
  obj_mp  = ModPath.initial;
}

let initial = {
  lib_stk = [];
  path_prefix = initial_prefix;
}

let synterp_state = ref initial
let interp_state = ref []

let comp_name = ref (None : DirPath.t option)

let contents () = !synterp_state.lib_stk @ !interp_state

let start_compilation s mp =
  if !comp_name != None then
    CErrors.user_err Pp.(str "compilation unit is already started");
  assert (List.is_empty !synterp_state.lib_stk);
  assert (List.is_empty !interp_state);
  if Global.sections_are_opened () then (* XXX not sure if we need this check *)
    CErrors.user_err Pp.(str "some sections are already opened");
  let prefix = Nametab.{ obj_dir = s; obj_mp = mp } in
  comp_name := Some s;
  let initial_stk = [ CompilingLibrary prefix, [] ] in
  let st = {
    path_prefix = prefix;
    lib_stk = initial_stk;
  }
  in
  synterp_state := st;
  interp_state := initial_stk

let end_compilation_checks dir =
  let () = match find_entries_p is_opening_node !interp_state with
    | [] -> ()
    | es -> CErrors.user_err (open_blocks_message es) in
  let () =
    match !comp_name with
      | None -> CErrors.anomaly (Pp.str "There should be a module name...")
      | Some m ->
          if not (Names.DirPath.equal m dir) then
            CErrors.anomaly Pp.(str "The current open module has name"
              ++ spc () ++ DirPath.print m ++ spc () ++ str "and not"
              ++ spc () ++ DirPath.print m ++ str ".");
  in
  ()

let end_compilation dir =
  end_compilation_checks dir;
  let (syntax_after,_,syntax_before) = split_lib_at_opening !synterp_state.lib_stk in
  let (after,_,before) = split_lib_at_opening !interp_state in
  assert (List.is_empty syntax_before);
  assert (List.is_empty before);
  comp_name := None;
  let syntax_after = classify_segment syntax_after in
  let after = classify_segment after in
  !synterp_state.path_prefix, after, syntax_after

  (* State and initialization. *)

  type frozen = {
    comp_name : DirPath.t option;
    synterp_state : t;
    interp_state : library_segment;
  }

  let freeze () = {
    comp_name = !comp_name;
    synterp_state = !synterp_state;
    interp_state = !interp_state;
  }

  let unfreeze st =
  comp_name := st.comp_name;
  synterp_state := st.synterp_state;
  interp_state := st.interp_state

  let drop_objects st =
    let drop_node = function
      | CompilingLibrary _ as x -> x
      | OpenedModule (it,e,op,_) ->
        OpenedModule(it,e,op,Summary.empty_frozen)
      | OpenedSection (op, _) ->
        OpenedSection(op,Summary.empty_frozen)
    in
    let lib_synterp_stk = List.map (fun (node,_) -> drop_node node, []) st.synterp_state.lib_stk in
    let synterp_state = { st.synterp_state with lib_stk = lib_synterp_stk } in
    let lib_interp_stk = List.map (fun (node,_) -> drop_node node, []) st.interp_state in
    let interp_state = lib_interp_stk in
    { comp_name = st.comp_name; synterp_state; interp_state }

  let init () =
    unfreeze { comp_name = None; synterp_state = initial; interp_state = [] };
    Summary.init_summaries ()

  let pr_node = let open Pp in function
  | CompilingLibrary prefix ->
    str "Library " ++ Nametab.pr_object_prefix prefix ++ str" = struct"
  | OpenedModule(is_type, export, prefix, fs) ->
    str "Module " ++ str(if is_type then "Type " else "") ++ Nametab.pr_object_prefix prefix ++ str" = sig"
  | OpenedSection(prefix, fs) ->
    str "Section " ++ Nametab.pr_object_prefix prefix

  let pr_segment l =
    Pp.(pr_vertical_list (fun (node, o) -> pr_node node ++ fnl () ++ pr_vertical_list Libobject.pr_libobject o) l)

  let print_state st =
    let open Pp in
    str "Current prefix: " ++ Nametab.pr_object_prefix st.path_prefix ++ fnl () ++
    str "Lib stack: " ++ pr_segment st.lib_stk

  let print () =
    let open Pp in
    str "Compilation unit name: " ++ pr_opt_default (fun () -> str"(none)") DirPath.print !comp_name ++ fnl () ++
    str "Synterp state:" ++ fnl() ++
    print_state !synterp_state ++ fnl() ++
    str "Interp state:" ++ fnl() ++
    pr_segment !interp_state

end

let library_dp () =
  match !State.comp_name with Some m -> m | None -> Libnames.default_library

(* [path_prefix] is a pair of absolute dirpath and a pair of current
   module path and relative section path *)

let prefix () = !State.synterp_state.path_prefix
let cwd () = !State.synterp_state.path_prefix.Nametab.obj_dir
let current_mp () = !State.synterp_state.path_prefix.Nametab.obj_mp
let current_sections () = Safe_typing.sections_of_safe_env (Global.safe_env())

let sections_depth () = match current_sections() with
  | None -> 0
  | Some sec -> Section.depth sec

let sections_are_opened () =
  match split_lib_at_opening !State.synterp_state.lib_stk with
  | (_, OpenedSection _, _) -> true
  | _ -> false

let cwd_except_section () =
  Libnames.pop_dirpath_n (sections_depth ()) (cwd ())

let current_dirpath sec =
  Libnames.drop_dirpath_prefix (library_dp ())
    (if sec then cwd () else cwd_except_section ())

let make_path id = Libnames.make_path (cwd ()) id

let make_path_except_section id =
  Libnames.make_path (cwd_except_section ()) id

let make_kn id =
  let mp = current_mp () in
  Names.KerName.make mp (Names.Label.of_id id)

let make_foname id = make_oname !State.synterp_state.path_prefix id

(* Adding operations. *)

let dummylib = CompilingLibrary
    {Nametab.obj_dir = DirPath.initial;
     Nametab.obj_mp = ModPath.MPfile DirPath.initial;
    }

let error_still_opened s oname =
  CErrors.user_err Pp.(str "The " ++ str s ++ str " "
    ++ Id.print (prefix_id oname) ++ str " is still opened.")

let recalc_path_prefix () =
  let path_prefix = match pi2 (split_lib_at_opening !State.synterp_state.lib_stk) with
    | CompilingLibrary dir
    | OpenedModule (_, _, dir, _)
    | OpenedSection (dir, _) -> dir
  in
  State.synterp_state := { !State.synterp_state with path_prefix }

let pop_path_prefix () =
  let op = !State.synterp_state.path_prefix in
  State.synterp_state := {
    !State.synterp_state
    with path_prefix = Nametab.{
        op with obj_dir = Libnames.pop_dirpath op.obj_dir;
      } }

(* Modules. *)

(* Returns true if we are inside an opened module or module type *)
let is_module_or_modtype () =
  match Safe_typing.module_is_modtype (Global.safe_env ()) with
  | [] -> false
  | _ -> true

let is_modtype () =
  let modules = Safe_typing.module_is_modtype (Global.safe_env ()) in
  List.exists (fun x -> x) modules

let is_modtype_strict () =
  match Safe_typing.module_is_modtype (Global.safe_env ()) with
  | b :: _ -> b
  | [] -> false

let is_module () =
  let modules = Safe_typing.module_is_modtype (Global.safe_env ()) in
  List.exists (fun x -> not x) modules

(* Discharge tables *)

(* At each level of section, we remember
   - the list of variables in this section
   - the list of variables on which each constant depends in this section
   - the list of variables on which each inductive depends in this section
   - the list of substitution to do at section closing
*)

let sections () = Safe_typing.sections_of_safe_env @@ Global.safe_env ()

let force_sections () = match Safe_typing.sections_of_safe_env (Global.safe_env()) with
  | Some s -> s
  | None -> CErrors.user_err Pp.(str "No open section.")

let section_segment_of_constant con =
  Section.segment_of_constant con (force_sections ())

let section_segment_of_inductive kn =
  Section.segment_of_inductive kn (force_sections ())

let section_segment_of_reference = let open GlobRef in function
| ConstRef c -> section_segment_of_constant c
| IndRef (kn,_) | ConstructRef ((kn,_),_) ->
  section_segment_of_inductive kn
| VarRef _ -> Cooking.empty_cooking_info

let is_in_section ref = match sections () with
  | None -> false
  | Some sec ->
    Section.is_in_section (Global.env ()) ref sec

let section_instance ref =
  Cooking.instance_of_cooking_info (section_segment_of_reference ref)

let discharge_item = Libobject.(function
  | ModuleObject _ | ModuleTypeObject _ | IncludeObject _ | KeepObject _
  | ExportObject _ -> None
  | AtomicObject obj -> discharge_object obj)

(* Misc *)

let mp_of_global = let open GlobRef in function
  | VarRef id -> !State.synterp_state.path_prefix.Nametab.obj_mp
  | ConstRef cst -> Names.Constant.modpath cst
  | IndRef ind -> Names.Ind.modpath ind
  | ConstructRef constr -> Names.Construct.modpath constr

let rec split_modpath = function
  |Names.MPfile dp -> dp, []
  |Names.MPbound mbid -> library_dp (), [Names.MBId.to_id mbid]
  |Names.MPdot (mp,l) ->
    let (dp,ids) = split_modpath mp in
    (dp, Names.Label.to_id l :: ids)

let library_part = function
  | GlobRef.VarRef id -> library_dp ()
  | ref -> ModPath.dp (mp_of_global ref)

let discharge_proj_repr p =
  let ind = Projection.Repr.inductive p in
  let sec = section_segment_of_reference (GlobRef.IndRef ind) in
  Cooking.discharge_proj_repr sec p

module type LibActions = sig

  val stage : Summary.Stage.t
  val check_mod_fresh : is_type:bool -> Nametab.object_prefix -> Id.t -> unit
  val check_section_fresh : DirPath.t -> Id.t -> unit
  val open_section : Id.t -> unit

  val push_section_name : DirPath.t -> unit

  val close_section : Summary.frozen -> unit

  val add_entry : node -> unit
  val add_leaf_entry : Libobject.t -> unit
  val start_mod : is_type:is_type -> export -> Id.t -> ModPath.t -> Summary.frozen -> Nametab.object_prefix

  val get_lib_stk : unit -> library_segment
  val set_lib_stk : library_segment -> unit

  val pop_path_prefix : unit -> unit
  val recalc_path_prefix : unit -> unit

end

module SynterpActions : LibActions = struct

  let stage = Summary.Stage.Synterp

  let check_mod_fresh ~is_type prefix id =
    let exists =
      if is_type then Nametab.exists_cci (Libnames.make_path prefix.Nametab.obj_dir id)
      else Nametab.exists_module prefix.Nametab.obj_dir
    in
    if exists then
      CErrors.user_err Pp.(Id.print id ++ str " already exists.")

  let check_section_fresh obj_dir id =
    if Nametab.exists_dir obj_dir then
      CErrors.user_err Pp.(Id.print id ++ str " already exists.")

  let push_section_name obj_dir =
    Nametab.(push_dir (Until 1) obj_dir (GlobDirRef.DirOpenSection obj_dir))

  let close_section fs = Summary.unfreeze_summaries ~partial:true fs

  let add_entry node =
    State.synterp_state := { !State.synterp_state with lib_stk = (node,[]) :: !State.synterp_state.lib_stk }

  let add_leaf_entry leaf =
    let lib_stk = match !State.synterp_state.lib_stk with
      | [] ->
        (* top_printers does set_bool_option_value which adds a leaf *)
        if !Flags.in_debugger then [dummylib, [leaf]] else assert false
      | (node, leaves) :: rest -> (node, leaf :: leaves) :: rest
    in
    State.synterp_state := { !State.synterp_state with lib_stk }

  (* Returns the opening node of a given name *)
  let start_mod ~is_type export id mp fs =
    let dir = Libnames.add_dirpath_suffix !State.synterp_state.path_prefix.Nametab.obj_dir id in
    let prefix = Nametab.{ obj_dir = dir; obj_mp = mp; } in
    check_mod_fresh ~is_type prefix id;
    add_entry (OpenedModule (is_type,export,prefix,fs));
    State.synterp_state := { !State.synterp_state with path_prefix = prefix } ;
    prefix

  let get_lib_stk () =
    !State.synterp_state.lib_stk

  let set_lib_stk stk =
    State.synterp_state := { !State.synterp_state with lib_stk = stk }

  let open_section id =
    let opp = !State.synterp_state.path_prefix in
    let obj_dir = Libnames.add_dirpath_suffix opp.Nametab.obj_dir id in
    let prefix = Nametab.{ obj_dir; obj_mp=opp.obj_mp; } in
    check_section_fresh obj_dir id;
    let fs = Summary.freeze_staged_summaries stage ~marshallable:false in
    add_entry (OpenedSection (prefix, fs));
    (*Pushed for the lifetime of the section: removed by unfreezing the summary*)
    push_section_name obj_dir;
    State.synterp_state := { !State.synterp_state with path_prefix = prefix }

  let pop_path_prefix () = pop_path_prefix ()
  let recalc_path_prefix () = recalc_path_prefix ()

end

module InterpActions : LibActions = struct

  let stage = Summary.Stage.Interp

  let check_mod_fresh ~is_type prefix id = ()
  let check_section_fresh _ _ = ()

  let push_section_name _ = ()
  let close_section fs = Global.close_section fs

  let add_entry node =
    State.interp_state := (node,[]) :: !State.interp_state

  let add_leaf_entry leaf =
    let lib_stk = match !State.interp_state with
      | [] ->
        (* top_printers does set_bool_option_value which adds a leaf *)
        if !Flags.in_debugger then [dummylib, [leaf]] else assert false
      | (node, leaves) :: rest -> (node, leaf :: leaves) :: rest
    in
    State.interp_state := lib_stk

  (* Returns the opening node of a given name *)
  let start_mod ~is_type export id mp fs =
    let prefix = !State.synterp_state.path_prefix in
    add_entry (OpenedModule (is_type,export,prefix,fs));
    prefix

  let get_lib_stk () =
    !State.interp_state

  let set_lib_stk stk =
    State.interp_state := stk

  let open_section id =
    Global.open_section ();
    let prefix = !State.synterp_state.path_prefix in
    let fs = Summary.freeze_staged_summaries stage ~marshallable:false in
    add_entry (OpenedSection (prefix, fs))

  let pop_path_prefix () = ()
  let recalc_path_prefix () = ()

end

let add_discharged_leaf obj =
  let newobj = Libobject.rebuild_object obj in
  Libobject.cache_object (prefix(),newobj);
  match Libobject.object_stage newobj with
  | Summary.Stage.Synterp ->
    SynterpActions.add_leaf_entry (AtomicObject newobj)
  | Summary.Stage.Interp ->
    InterpActions.add_leaf_entry (AtomicObject newobj)

let add_leaf obj =
  Libobject.cache_object (prefix(),obj);
  match Libobject.object_stage obj with
  | Summary.Stage.Synterp ->
    SynterpActions.add_leaf_entry (AtomicObject obj)
  | Summary.Stage.Interp ->
    InterpActions.add_leaf_entry (AtomicObject obj)

module LibVisitor(Actions : LibActions) = struct

let add_entry node = Actions.add_entry node
let add_leaf_entry obj = Actions.add_leaf_entry obj

let open_section id = Actions.open_section id

let find_opening_node id =
  let entry = match Actions.get_lib_stk () with
    | [] -> assert false
    | (CompilingLibrary _, _) :: _ ->
        CErrors.user_err Pp.(str "There is nothing to end.")
    | (entry, _) :: _ -> entry
  in
  let id' = prefix_id (node_prefix entry) in
  if not (Names.Id.equal id id') then
    CErrors.user_err Pp.(str "Last block to end has name "
      ++ Id.print id' ++ str ".");
  entry

let start_module = Actions.start_mod ~is_type:false
let start_modtype = Actions.start_mod ~is_type:true None

let end_mod ~is_type =
  CDebug.debug_synterp (fun () -> Pp.(str"Stack before end_mod: " ++ fnl () ++ State.pr_segment (Actions.get_lib_stk ())));
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
  let after = classify_segment after in
  (prefix, fs, after)

let end_module () = end_mod ~is_type:false
let end_modtype () = end_mod ~is_type:true

(* Restore lib_stk and summaries as before the section opening, and
   add a ClosedSection object. *)
let close_section () =
  let (secdecls,mark,before) = split_lib_at_opening (Actions.get_lib_stk ()) in
  let fs = match mark with
    | OpenedSection (_,fs) -> fs
    | _ -> CErrors.user_err Pp.(str "No opened section.")
  in
  Actions.set_lib_stk before;
  Actions.pop_path_prefix ();
  let newdecls = List.map discharge_item secdecls in
  Actions.close_section fs;
  List.iter (Option.iter add_discharged_leaf) newdecls

end

module type LibVisitorS = sig

  val find_opening_node : Id.t -> node

  val add_entry : node -> unit
  val add_leaf_entry : Libobject.t -> unit

  (** {6 Sections } *)
  val open_section : Id.t -> unit
  val close_section : unit -> unit

  (** {6 Modules and module types } *)
  val start_module :
    export -> module_ident -> ModPath.t ->
    Summary.frozen -> Nametab.object_prefix

  val start_modtype :
    module_ident -> ModPath.t ->
    Summary.frozen -> Nametab.object_prefix

  val end_module :
    unit ->
    Nametab.object_prefix * Summary.frozen * classified_objects

  val end_modtype :
    unit ->
    Nametab.object_prefix * Summary.frozen * classified_objects

end

module Synterp : LibVisitorS = LibVisitor(SynterpActions)
module Interp : LibVisitorS = LibVisitor(InterpActions)

let start_compilation s mp =
  State.start_compilation s mp

let end_compilation dir =
  State.end_compilation dir
