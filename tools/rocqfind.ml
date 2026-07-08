let panic fmt =
  Format.kfprintf (fun _ -> exit 1) Format.err_formatter (fmt ^^ "\n%!")

let usage ~prog () =
  Format.printf "Usage: %s [-I] [-Q] [-h|--help] PKG ...\n" prog

type config = {
  flag_I : bool;
  flag_Q : bool;
  pkgs : string list;
}

let parse_args ~prog args =
  let cfg = {flag_I = false; flag_Q = false; pkgs = []} in
  let handle_arg cfg arg =
    let is_flag arg = String.length arg > 0 && arg.[0] = '-' in
    match arg with
    | "-I"               -> {cfg with flag_I = true}
    | "-Q"               -> {cfg with flag_Q = true}
    | "-h" | "--help"    -> usage ~prog (); exit 0
    | _ when is_flag arg -> panic "Error: unrecognized flag %S." arg
    | _                  -> {cfg with pkgs = arg :: cfg.pkgs}
  in
  List.fold_left handle_arg cfg args

let rocqpath pkg =
  try Some(Fl_metascanner.lookup "rocqpath" [] pkg.Fl_package_base.package_defs)
  with Not_found -> None

let rec strip_trailing_current_dir dir =
  let parent = Filename.dirname dir in
  if Filename.basename dir = Filename.current_dir_name && parent <> dir then
    strip_trailing_current_dir parent
  else
    dir

let rocq_theory_dir pkg =
  let dir = strip_trailing_current_dir pkg.Fl_package_base.package_dir in
  Filename.concat dir "rocq.d"

let query_packages pkgs =
  Findlib.init ();
  let rocq_package_names () =
    let pkgs = Fl_package_base.list_packages () in
    let get_name pkg_name =
      let pkg = Fl_package_base.query pkg_name in
      match rocqpath pkg with
      | None -> None
      | Some _ -> Some(pkg_name)
    in
    List.filter_map get_name pkgs
  in
  let pkgs = if pkgs = [] then rocq_package_names () else pkgs in
  let pkgs = Fl_package_base.requires_deeply ~preds:[] pkgs in
  let static_libs =
    let preds = ["native"] in
    Fl_package_base.requires_deeply ~preds ["rocq-runtime.toplevel"]
  in
  let pkgs = List.filter (fun p -> not (List.mem p static_libs)) pkgs in
  let query pkg =
    let pkg = Fl_package_base.query pkg in
    (rocqpath pkg, pkg)
  in
  List.map query pkgs

let split_packages pkgs =
  let rocq_pkgs =
    let filter (rocqpath, pkg) =
      match rocqpath with
      | None    -> None
      | Some(p) -> Some(p, pkg)
    in
    List.filter_map filter pkgs
  in
  let plugins =
    let filter (rocqpath, pkg) =
      match rocqpath with
      | None    -> Some(pkg)
      | Some(_) -> None
    in
    List.filter_map filter pkgs
  in
  rocq_pkgs, plugins

module S = Set.Make(String)

let output_I done_dirs pkg =
  (* For sub-packages, the dir with the META is not the package dir. *)
  let dir = Filename.dirname pkg.Fl_package_base.package_meta in
  if not (S.mem dir !done_dirs) then begin
    done_dirs := S.add dir !done_dirs;
    Format.printf "-I %s\n%!" (Filename.quote dir)
  end

let output_Q (rocqpath, pkg) =
  let dir = rocq_theory_dir pkg in
  let dir = Filename.quote dir in
  Format.printf "-Q %s %s\n%!" dir rocqpath

let main ~prog args =
  let {flag_I; flag_Q; pkgs} = parse_args ~prog args in
  let (rocq_pkgs, plugins) = split_packages (query_packages pkgs) in
  match flag_I, flag_Q with
  | false, false ->
      let output_theory (mp, pkg) =
        Format.printf "%s %s\n%!" (rocq_theory_dir pkg) mp
      in
      List.iter output_theory rocq_pkgs
  | _    , _     ->
      let done_dirs = ref S.empty in
      if flag_Q then List.iter output_Q rocq_pkgs;
      if flag_I then List.iter (output_I done_dirs) plugins;
