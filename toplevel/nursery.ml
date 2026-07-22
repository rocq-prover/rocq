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
    (* TODO unmarshal required files before fork
       (need to parse args enough to find the file, then read it to find requires) *)
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
  let () = Coqinit.init_ocaml () in
  let opts, _ = Coqargs.parse_args ~init:Coqargs.default args in
  let boot_env = Boot.Env.maybe_init ~boot:opts.pre.boot ~coqlib:opts.config.coqlib
      ~warn_ignored_coqlib:CWarnings.warn_ignored_coqlib
  in
  let () = Coqinit.init_load_paths boot_env opts in
  (* nursery mode assumes vo_includes is constant *)
  let () = List.iter (fun x -> Loadpath.add_vo_path @@ to_vo_path x) opts.pre.vo_includes in

  loop self
