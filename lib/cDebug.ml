(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* [value] is the value set by [set_flag], [set_flags] and [set_debug_all],
   [get_flag] also takes the overrides into account *)
type flag = { name : string; value : bool ref }

type t = (unit -> Pp.t) -> unit

let debug = ref CString.Map.empty

(* Used to remember level of Set Debug "all" for debugs created by
   plugins dynlinked after the Set *)
let all_flag = ref false

(* The overrides set by [set_override]. They are not reported by [get_flags],
   hence not saved in the summary. *)
let overrides = ref CString.Map.empty

let find_override name =
  if CString.Map.is_empty !overrides then None
  else match CString.Map.find_opt name !overrides with
    | Some _ as o -> o
    | None -> CString.Map.find_opt "all" !overrides

(* Backtrace recording is global state of OCaml: while it is overridden,
   the setting of the commands is kept here *)
let backtrace_setting = ref None

let get_backtrace_setting () = match !backtrace_setting with
  | Some b -> b
  | None -> Printexc.backtrace_status ()

let set_debug_backtrace b = match !backtrace_setting with
  | Some _ -> backtrace_setting := Some b
  | None -> Exninfo.record_backtrace b

let set_debug_all b =
  set_debug_backtrace b;
  CString.Map.iter (fun _ flag -> flag.value := b) !debug;
  all_flag := b

let get_flag flag = match find_override flag.name with
  | Some b -> b
  | None -> !(flag.value)

let create_full ~name () =
  let anomaly pp = CErrors.anomaly ~label:"CDebug.create" pp in
  let () = match name with
    | "all"|"backtrace" -> anomaly Pp.(str"The debug name \""++str name++str"\" is reserved.")
    | _ ->
      if CString.Map.mem name !debug then
        anomaly Pp.(str "The debug name \"" ++ str name ++ str "\" is already used.")
  in
  let pp x =
    Feedback.msg_debug Pp.(hv 2 (str "[" ++ str name ++ str "]" ++ spc() ++ x))
  in
  let flag = { name; value = ref !all_flag } in
  debug := CString.Map.add name flag !debug;
  let pp x =
    if get_flag flag
    then pp (x ())
  in
  flag, pp

let create ~name () =
  snd (create_full ~name ())

let set_flag flag v = flag.value := v

let warn_unknown_debug = CWarnings.create ~name:"unknown-debug-flag"
    Pp.(fun name -> str "There is no debug flag \"" ++ str name ++ str "\".")

let get_flags () =
  let pp_flag name flag = if flag then name else "-"^name in
  let flags =
    CString.Map.fold
      (fun name v acc -> pp_flag name !(v.value) :: acc)
      !debug []
  in
  let all = pp_flag "all" !all_flag in
  let bt = pp_flag "backtrace" (get_backtrace_setting ()) in
  String.concat "," (all::bt::flags)

exception Error

let parse_flags s =
  let parse_flag s =
    if CString.is_empty s then raise Error
    else if s.[0] = '-'
    then String.sub s 1 (String.length s - 1), false
    else s, true
  in
  try
    Some (CList.map parse_flag @@ String.split_on_char ',' s)
  with Error -> None

let set_flags s = match parse_flags s with
  | None -> CErrors.user_err Pp.(str "Syntax error in debug flags.")
  | Some flags ->
    let set_one_flag (name,b) = match name with
      | "all" -> set_debug_all b
      | "backtrace" -> set_debug_backtrace b
      | _ -> match CString.Map.find_opt name !debug with
        | None -> warn_unknown_debug name
        | Some flag -> flag.value := b
    in
    List.iter set_one_flag flags

let set_override name v =
  let () = match name with
    | "all" | "backtrace" -> ()
    | _ ->
      if not (CString.Map.mem name !debug) then
        CErrors.user_err Pp.(str "There is no debug flag \"" ++ str name ++ str "\".")
  in
  let setting = get_backtrace_setting () in
  overrides := begin match v with
    | None -> CString.Map.remove name !overrides
    | Some b -> CString.Map.add name b !overrides
  end;
  match find_override "backtrace" with
  | None ->
    backtrace_setting := None;
    Exninfo.record_backtrace setting
  | Some b ->
    backtrace_setting := Some setting;
    Exninfo.record_backtrace b

let get_override name = CString.Map.find_opt name !overrides

let get_flag_values () =
  let flags =
    CString.Map.fold (fun name flag acc -> (name, get_flag flag) :: acc) !debug []
  in
  let all = Option.default !all_flag (get_override "all") in
  ("all", all) :: ("backtrace", Printexc.backtrace_status ()) :: flags

let misc, pp_misc = create_full ~name:"misc" ()
