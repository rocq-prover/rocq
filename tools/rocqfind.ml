let panic fmt =
  Format.kfprintf (fun _ -> exit 1) Format.err_formatter (fmt ^^ "\n%!")

let usage () =
  let p = Sys.argv.(0) in
  Format.printf "Usage: %s [--cmxs] [-I] [-Q] [-h | --help] PKG ...\n%!" p

let (cmxs, flags_I, flags_Q, pkgs) =
  let cmxs = ref false in
  let flags_I = ref false in
  let flags_Q = ref false in
  let pkgs = ref [] in
  let interp_args arg =
    let is_flag arg = String.length arg > 0 && arg.[0] = '-' in
    match arg with
    | "--cmxs"           -> cmxs := true
    | "-I"               -> flags_I := true
    | "-Q"               -> flags_Q := true
    | "-h" | "--help"    -> usage (); exit 0
    | _ when is_flag arg -> panic "Error: unrecognized flag %S." arg
    | _                  -> pkgs := arg :: !pkgs
  in
  for i = 1 to Array.length Sys.argv - 1 do
    interp_args Sys.argv.(i)
  done;
  (!cmxs, !flags_I, !flags_Q, List.rev !pkgs)

let pkgs =
  Findlib.init ();
  let preds = ["native"] in
  let static_libs =
    Fl_package_base.requires_deeply ~preds ["rocq-runtime.toplevel"]
  in
  let pkgs =
    let pkgs = Fl_package_base.requires_deeply ~preds:[] pkgs in
    List.filter (fun p -> not (List.mem p static_libs)) pkgs
  in
  let query pkg =
    let pkg = Fl_package_base.query pkg in
    let rocqpath =
      try Some(Fl_metascanner.lookup "rocqpath" [] pkg.package_defs)
      with Not_found -> None
    in
    (rocqpath, pkg)
  in
  List.map query pkgs

let rocq_pkgs =
  let filter (rocqpath, pkg) =
    match rocqpath with
    | None    -> None
    | Some(p) -> Some(p, pkg)
  in
  List.filter_map filter pkgs

let plugins =
  let filter (rocqpath, pkg) =
    match rocqpath with
    | None    -> Some(pkg)
    | Some(_) -> None
  in
  List.filter_map filter pkgs

let output_cmxs pkg =
  let dir = pkg.Fl_package_base.package_dir in
  let defs = pkg.Fl_package_base.package_defs in
  try
    let plugin = Fl_metascanner.lookup "plugin" ["native"] defs in
    let plugin = Filename.concat dir plugin in
    let plugin = Filename.quote plugin in
    Format.printf "%s\n%!" plugin
  with Not_found -> ()

module S = Set.Make(String)
let done_dirs = ref S.empty

let output_I pkg =
  (* For sub-packages, the dir with the META is not the package dir. *)
  let dir = Filename.dirname pkg.Fl_package_base.package_meta in
  if not (S.mem dir !done_dirs) then begin
    done_dirs := S.add dir !done_dirs;
    Format.printf "-I %s\n%!" (Filename.quote dir)
  end

let output_Q (rocqpath, pkg) =
  let dir = pkg.Fl_package_base.package_dir in
  let dir = Filename.concat dir "rocq.d" in
  let dir = Filename.quote dir in
  Format.printf "-Q %s %s\n%!" dir rocqpath

let _ =
  if cmxs    then List.iter output_cmxs plugins;
  if flags_I then List.iter output_I    plugins;
  if flags_Q then List.iter output_Q    rocq_pkgs
