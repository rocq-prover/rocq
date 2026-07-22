(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let to_vo_path (x:Coqargs.vo_path) : Loadpath.vo_path = {
  implicit = x.implicit;
  unix_path = x.unix_path;
  coq_path = Libnames.dirpath_of_string x.rocq_path;
  recursive = true;
  installed = false;
  }

let cache = ref Names.DirPath.Map.empty

let fs_intern dp =
  match Names.DirPath.Map.find_opt dp !cache with
  | Some (v, prov) -> Ok v, prov
  | None ->
    Printf.eprintf "non cached require %s\n%!" (Names.DirPath.to_string dp);
    Vernacinterp.base_fs_intern dp

let cache_intern dp =
  match Names.DirPath.Map.find_opt dp !cache with
  | Some (v, _) -> Some v
  | None ->
    match Vernacinterp.base_fs_intern dp with
    | exception e when CErrors.noncritical e -> None
    | Ok v, prov ->
      (* Printf.eprintf "nursery loaded %s\n%!" (Names.DirPath.to_string dp); *)
      cache := Names.DirPath.Map.add dp (v,prov) !cache;
      Some v
    | Error _, _ -> None

let rec rec_intern dp =
  if Names.DirPath.Map.mem dp !cache then ()
  else match cache_intern dp with
    | None -> ()
    | Some lib ->
      Array.iter (fun (dp, _) -> rec_intern dp) (Library.library_deps lib)

let intern_require_command from qids =
  (* could also translate Coq-Stdlib but whatever *)
  let root = match from with
    | None -> None
    | Some from ->
      let (hd, tl) = Libnames.repr_qualid from in
      Some (Libnames.add_dirpath_suffix hd tl)
  in
  let locate qid =
    let open Loadpath in
    match locate_qualified_library ?root qid with
    | Ok (dir,_) -> Some dir
    | Error _ -> None
  in
  let modrefl = List.filter_map locate qids in
  List.iter rec_intern modrefl

let rec intern_required lexbuf =
  let open Coqdeplib.Lexer in
  let qualid s = Libnames.qualid_of_string (String.concat "." s) in
  match coq_action lexbuf with
  | exception Fin_fichier -> ()
  | Require (from, sl) ->
    let from = Option.map qualid from in
    let sl = List.map (fun (_, s) -> qualid s) sl in
    intern_require_command from sl;
    intern_required lexbuf
  | Declare _ | Load _ | External _ ->
    (* could try to look into Load but whatever *)
    intern_required lexbuf

let intern_required_injection = function
  | Coqargs.RequireInjection { prefix; lib; } ->
    intern_require_command (Option.map Libnames.qualid_of_string prefix)
      [Libnames.qualid_of_string lib]
  | _ -> ()

let intern_required = function
  | "--kind=compile" :: args ->
    let () =
      try
        let opts, _ = Coqargs.parse_args ~init:Coqargs.default args in
        List.iter intern_required_injection (Coqargs.injection_commands opts);
        let f = List.find (fun a -> Filename.extension a = ".v") args in
        let ch = open_in f in
        let lexbuf = Lexing.from_channel ~with_positions:false ch in
        intern_required lexbuf;
        close_in ch
      with e when CErrors.noncritical e -> ()
    in
    ()
  | _ -> ()

let rec loop self =
  let ch_in = try open_in_bin ".nursery-in" with Sys.Break -> exit 0 in
  match input_line ch_in with
  | "Exit" -> ()
  | "Run" ->
    let args : string list = Marshal.from_channel ch_in in
    (* don't keep ch_in open and instead reopen each loop
       because I can't figure out how to wait for a new writer *)
    close_in ch_in;
    (* Printf.eprintf "nursery running %s\n%!" (String.concat " " args); *)
    let () = intern_required args in
    let pid = Unix.fork () in
    if pid = 0 then
      (* XXX redirect stdout/stderr to other process's fds? is that even possible?
         (doesn't matter in rocq makefile operation
         because it all goes to the make caller's stdout/stderr) *)
      self args
    else
      let _, status = Unix.waitpid [] pid in
      let status = match status with
        | WEXITED i -> i
        | WSIGNALED i -> i
        | WSTOPPED _ -> assert false
      in
      let ch_out = open_out ".nursery-out" in
      Printf.fprintf ch_out "%d\n%!" status;
      close_out ch_out;
      loop self
  | s -> Printf.eprintf "Unknown nursery command %S.\n%!" s; exit 1

let start self args =
  let () = Exninfo.record_backtrace true in
  let () = Flags.nursery := true in
  let () = Vernacextend.static_linking_done () in
  let () = Vernacinterp.set_fs_intern fs_intern in
  let () = Coqinit.init_ocaml () in
  let opts, _ = Coqargs.parse_args ~init:Coqargs.default args in
  let boot_env = Boot.Env.maybe_init ~boot:opts.pre.boot ~coqlib:opts.config.coqlib
      ~warn_ignored_coqlib:CWarnings.warn_ignored_coqlib
  in
  let () = Coqinit.init_load_paths boot_env opts in
  (* nursery mode assumes vo_includes is constant *)
  let () = List.iter (fun x -> Loadpath.add_vo_path @@ to_vo_path x) opts.pre.vo_includes in

  loop self
