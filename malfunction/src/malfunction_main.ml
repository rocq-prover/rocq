open Malfunction


let usage () =
  Printf.fprintf stderr "%s" @@
    "Malfunction v0.1. Usage:\n"^
    "   malfunction compile [-v] [-thread] [-linkpkg] [-dontlink pack1,...,packn] [-package pack1,...packn] [-o output] input.mlf\n" ^
    "     Compile input.mlf to an executable using ocamlfind\n" ^
    "   malfunction cmx [-v] [-shared] [-package pack1,...,packn] [-for-pack s] input.mlf\n" ^
    "     Compile input.mlf to input.cmx, for linking with ocamlopt.\n"^
    "   malfunction cmo [-v] [-shared] [-package pack1,...,packn] [-for-pack s] input.mlf\n" ^
    "     Compile input.mlf to input.cmo (bytecode), for linking with ocamlc.\n" ^
    "   malfunction eval\n" ^
    "     Run a REPL to evaluate expressions with the interpreter\n\n" ^
    "   malfunction fmt\n" ^
    "     Reindent the s-expression on standard input\n";
  2

let repl () =
  let lexbuf = Lexing.from_channel stdin in
  let rec loop () =
    Printf.printf "# %!";
    with_error_reporting Format.std_formatter () (fun () ->
      let exp = Malfunction_parser.read_expression lexbuf in
      match Malfunction_interpreter.eval exp with
      | v -> Format.printf "%a\n%!" Malfunction_sexp.print 
         (Malfunction_interpreter.render_value v);
         loop ()
      | exception (Malfunction_interpreter.Error s) ->
         Format.printf "Undefined behaviour: %s\n%!" s);
    loop () in
  try loop () with End_of_file -> ()

let run mode options impl output =
  Findlib.init ();
  match mode, impl with
  | `Cmx, Some file ->
     with_error_reporting Format.std_formatter 1 (fun () ->
       let _ = Malfunction_compiler.compile_cmx ~options file in
       0)
  | `Cmo, Some file ->
     with_error_reporting Format.std_formatter 1 (fun () ->
       let _ = Malfunction_compiler.compile_cmo ~options file in
       0)
  | `Compile, Some file ->
     with_error_reporting Format.std_formatter 1 (fun () ->
       let tmpfiles = Malfunction_compiler.compile_cmx ~options file in
       let output = match output with
         | None -> Compenv.output_prefix file
         | Some out -> out in
       let res = Malfunction_compiler.link_executable ~options output tmpfiles in
       Malfunction_compiler.delete_temps tmpfiles;
       res)
  | `Eval, Some _file ->
     0
  | `Eval, None ->
     repl (); 0
  | `Fmt, impl ->
     let lexbuf = Lexing.from_channel (match impl with Some f -> open_in f | None -> stdin) in
     Malfunction_sexp.(read_only_sexp lexbuf |> print Format.std_formatter);
     Format.printf "\n%!";
     0
  | _ -> usage ()


let parse_args args =
  let impl = ref None in
  let output = ref None in
  let opts = ref [] in
  let rec parse_opts mode = function
    | "-v" :: rest -> opts := `Verbose :: !opts; parse_opts mode rest
    | "-o" :: o :: rest -> output := Some o; parse_opts mode rest
    | "-shared" :: rest -> opts := `Shared :: !opts; parse_opts mode rest
    | "-for-pack" :: o :: rest -> opts := `ForPack o :: !opts; parse_opts mode rest
    | "-I" :: s :: rest -> opts := `Include s :: !opts; parse_opts mode rest
    | "-package" :: s :: rest -> opts := `Package s :: !opts; parse_opts mode rest
    | "-dontlink" :: s :: rest -> 
      if mode = `Compile then (opts := `Dontlink s :: !opts; parse_opts mode rest)
      else usage ()
    | "-linkpkg" :: rest -> 
      if mode = `Compile then (opts := `Linkpkg :: !opts; parse_opts mode rest)
      else usage ()
    | "-g" :: rest -> opts := `Debug :: !opts; parse_opts mode rest
    | "-rectypes" :: rest -> opts := `Rectypes :: !opts; parse_opts mode rest
    | "-thread" :: rest -> 
        if mode = `Compile then (opts := `Thread :: !opts; parse_opts mode rest)
        else usage ()
    | "-O2" :: rest -> opts := `Optimize :: !opts; parse_opts mode rest
    | i :: rest ->
       (match !impl with None -> (impl := Some i; parse_opts mode rest) | _ -> usage ())
    | [] -> run mode !opts !impl !output in
  match args with
  | "cmx" :: rest -> parse_opts `Cmx rest
  | "cmo" :: rest -> parse_opts `Cmo rest
  | "compile" :: rest -> parse_opts `Compile rest
  | "eval" :: rest -> parse_opts `Eval rest
  | "fmt" :: rest -> parse_opts `Fmt rest
  | _ -> usage ()

(*
let () =
  if not Config.flambda then begin
    Format.fprintf Format.err_formatter 
      "Malfunction requires a version of OCaml with Flambda enabled\n\
       Try \"opam switch 4.03.0+flambda\"\n";
    exit 1
  end
 *)

let _ = exit (parse_args (List.tl (Array.to_list Sys.argv)))
