let git args =
  match Unix.open_process_args_in "git" (Array.of_list ("git" :: args)) with
  | exception Unix.Unix_error _ -> None
  | ch ->
    let rec read accu = match input_line ch with
    | line -> read (line :: accu)
    | exception End_of_file -> List.rev accu
    in
    let lines = read [] in
    match Unix.close_process_in ch with
    | Unix.WEXITED 0 -> Some lines
    | _ -> None

let () =
  Unix.putenv "LANG" "C";
  match git ["rev-parse"; "--git-dir"] with
  | None -> prerr_endline "skipping make_git_revision: git dir not found"
  | Some _ ->
    let branches = Option.value ~default:[] (git ["branch"; "-a"]) in
    let branch =
      List.fold_left (fun accu line ->
          if String.length line >= 2 && String.sub line 0 2 = "* " then
            String.sub line 2 (String.length line - 2)
          else accu) "" branches
    in
    let hash = match git ["log"; "-1"; "--pretty=format:%H"] with
    | Some (h :: _) -> h
    | _ -> ""
    in
    Printf.printf "%s:%s,%s\n%s\n" (Unix.gethostname ()) (Sys.getcwd ()) branch hash
