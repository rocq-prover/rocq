open Malfunction
open Malfunction_parser
open Malfunction_interpreter

exception ReifyFailure of string
let rec reify = function
| Block (n, xs) -> reify_block n xs
| Vec (`Array, xs) -> reify_block 0 xs
| Vec (`Bytevec, xs) ->
   let to_char = function
     | Int (`Int, n) when 0 <= Z.to_int n && Z.to_int n < 256 ->
        String.make 1 (Char.chr (Z.to_int n))
     | _ -> raise (ReifyFailure "reify: noncharacter in string") in
   Obj.repr (String.concat "" (List.map to_char (Array.to_list xs)))
| Int (ty, n) -> Obj.(match ty with
  | `Int -> repr (Z.to_int n)
  | `Int32 -> repr (Z.to_int32 n)
  | `Int64 -> repr (Z.to_int64 n)
  | `Bigint -> repr n)
| Float f -> Obj.repr f
| Func _ -> raise (ReifyFailure "reify: functional value")
| Thunk _ -> raise (ReifyFailure "reify: lazy value")

and reify_block n xs =
  let o = Obj.new_block n (Array.length xs) in
  for i = 0 to Array.length xs - 1 do
    Obj.set_field o i (reify xs.(i))
  done;
  o

let check xs =
  Array.iter (fun a ->
  Stdlib.print_char
    (if Stdlib.(=) (Marshal.from_channel Stdlib.stdin) a then
        'Y'
     else
        'N')) xs;
  Stdlib.flush_all ()

let check_stub = "
  (lambda ($xs)
    (seq
      (apply (global $Z $of_string) \"42\") ; ensure zarith loaded for unmarshalling
      (apply (global $Array $iter) (lambda ($x)
        (apply (global $Stdlib $print_char)
          (if (== 0
                (apply (global $Stdlib $compare)
                       $x
                       (apply (global $Marshal $from_channel) (global $Stdlib $stdin))))
              89
              78))) $xs)
      (apply (global $Stdlib $print_newline) 0)))"

type test_result =
  [ `Bad_test of string (* expected output had undefined behaviour or was a function *)
  | `Undefined of string (* testcase had undefined behaviour *)
  | `Crash of string (* compiled executable failed to run or crashed, even though testcase had defined behaviour *)
  | `Different (* interpreter and compiler agree that testcase does not match expected output *)
  | `Inconsistent (* interpreter and compiler disagree whether testcase matches expected output *)
  | `Match ] (* interpreter and compiler agree that testcase matches expected output *)


exception HarnessFailed of string

let exec_name = "malfunction_test_exec"

let try_run_tests cases =
  if Sys.file_exists exec_name then
    raise (HarnessFailed ("file exists: "^exec_name));
  let checker = Malfunction_parser.read_expression
    (Lexing.from_string check_stub) in
  let testcases = cases |> List.map @@ function
    | `Bad_test _ | `Undefined _ -> Mnum (`Int 0)
    | `Match (test, _) | `NoMatch (test, _) -> test in

  let temps = ref None in
  let delete_temps () =
    Misc.remove_file exec_name;
    match !temps with Some t -> Malfunction_compiler.delete_temps t | None -> () in

  let options = [`Package "zarith"; `Linkpkg] in
  begin match
    Mmod ([`Unnamed (Mapply (checker, [Mblock (0, testcases)]))], [])
    |> Malfunction_compiler.compile_module ~options ~filename:exec_name
    |> (fun t -> temps := Some t; t)
    |> Malfunction_compiler.link_executable ~options exec_name
  with
  | 0 -> ()
  | _ -> delete_temps (); raise (HarnessFailed "Link error")
  | exception e ->
      Location.report_exception Format.str_formatter e;
      delete_temps ();
      raise (HarnessFailed (Format.flush_str_formatter ())) end;
  let (rd, wr) = Unix.open_process ("./" ^ exec_name) in
  cases
  |> List.map (function
    | `Bad_test _ | `Undefined _ -> Obj.repr 0
    | `Match (_, obj) | `NoMatch (_, obj) -> obj)
  |> List.iter (fun x -> Marshal.to_channel wr x []);
  flush wr;
  let answer = try input_line rd with End_of_file -> "" in
  let result = Unix.close_process (rd, wr) in
  delete_temps ();
  match result with
  | Unix.WEXITED 0 when String.length answer = List.length cases ->
     cases |> List.mapi (fun i c -> match c, answer.[i] with
     | (`Bad_test _ | `Undefined _) as x, _ -> x
     | `Match _, 'Y' -> `Match
     | `NoMatch _, 'N' -> `Different
     | `Match _, 'N' -> `Inconsistent
     | `NoMatch _, 'Y' -> `Inconsistent
     | _, c -> `Crash ("output produced '" ^ String.make 1 c ^ "'"))
  | _ -> raise (HarnessFailed "executable failed")

let run_tests cases =
  try
    try_run_tests cases
  with
    (* failed to run all at once, run them one at a time to isolate crashing case *)
    HarnessFailed _ ->
      cases |> List.map @@ fun x ->
        try List.hd (try_run_tests [x]) with
          HarnessFailed s -> `Crash s

let load_testcases filename =
  let lexbuf = Lexing.from_channel (open_in filename) in
  Lexing.(lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_fname = filename});
  let rec read_testcases acc =
    let open Malfunction_sexp in
    match read_next_sexp lexbuf with
    | loc, List [_, Atom "test"; test; exp] ->
       read_testcases ((`Test, loc,
                        Malfunction_parser.parse_expression test,
                        Malfunction_parser.parse_expression exp) :: acc)
    | loc, List [_, Atom "test-differ"; test; exp] ->
       read_testcases ((`TestDiffer, loc,
                        Malfunction_parser.parse_expression test,
                        Malfunction_parser.parse_expression exp) :: acc)
    | loc, List [_, Atom "test-undefined"; test] ->
       read_testcases ((`TestUndef, loc,
                        Malfunction_parser.parse_expression test,
                        Malfunction_parser.parse_expression (loc, Atom "0")) :: acc)
    | loc, _ -> raise (SyntaxError (loc, "Bad test"))
    | exception End_of_file -> List.rev acc in
  read_testcases []

let load_testcases_markdown filename =
  let chan = open_in filename in
  let buflen = 1000 in
  let rec read_all () =
    let buf = Bytes.create buflen in
    match input chan buf 0 buflen with
    | 0 -> []
    | n -> Bytes.sub_string buf 0 n :: read_all () in
  let contents = String.concat "" (read_all ()) in
  let parse_string s =
    s |> Lexing.from_string |> Malfunction_sexp.read_only_sexp |> Malfunction_parser.parse_expression in
  let dummy_loc =
    let l = Lexing.{pos_fname = filename; pos_lnum = 0; pos_cnum = 0; pos_bol = 0} in
    l,l in
  let open Omd in
  let testcases = ref [] in
  let _ = Omd.of_string contents |> List.iter @@ function
    | Code_block (_, ("test" | " test"), s) ->
       let open Str in
       let (test, expect) = match split (regexp "\n=>") s with
         | [t; e] -> (parse_string t, parse_string e)
         | _ -> failwith @@ "Cannot parse testcase " ^ s in
       testcases := (`Test, dummy_loc, test, expect) :: !testcases;
       ()
    | _ -> ()
  in
  List.rev !testcases

let run_file parser filename =
  Format.printf "%s: %!" filename;
  match Malfunction.with_error_reporting (Format.std_formatter) None
    (fun () -> Some (parser filename))
  with
  | None -> Format.printf "parse error\n%!"; `SomeFailed
  | Some cases ->
     let results = cases
     |> List.map (fun (_ty, _loc, test, expect) ->
       match eval expect with
       | exception (Error s) -> `Bad_test s
       | expectRes -> match eval test, reify expectRes with
         | exception (Error s) -> `Undefined s
         | exception (ReifyFailure s) -> `Bad_test s
         | testRes, expectObj ->
            if compare testRes expectRes = 0 then
              `Match (test, expectObj)
            else
              `NoMatch (test, expectObj))
     |> run_tests in
     let passed = ref 0 in
     let describe (ty, ({Lexing.pos_lnum = line; _}, _), _, _) result =
       let say fmt =
         Format.printf "\n%s:%d: " filename line;
         let endline ppf =
           Format.fprintf ppf "\n%!" in
         Format.kfprintf endline Format.std_formatter fmt in
       begin match ty, result with
       | _, `Bad_test s -> say "bad test: %s" s
       | _, `Crash s -> say "crash: %s" s
       | _, `Inconsistent -> say "inconsistent results"
       | `Test, `Match
       | `TestUndef, `Undefined _
       | `TestDiffer, `Different -> incr passed
       | (`Test|`TestDiffer), `Undefined s -> say "undefined behaviour: %s" s
       | `TestUndef, (`Match|`Different) -> say "undefined behaviour not detected"
       | `Test, `Different -> say "values don't match"
       | `TestDiffer, `Match -> say "values match when not expected to" end;
     in
     List.iter2 describe cases results;
     Format.printf "\r%-25s [%d/%d] tests passed\n%!" (filename ^ ":") !passed (List.length cases);
     if !passed = List.length cases then `AllPassed else `SomeFailed

let rec run_all testfiles =
  let combine a b = match a, b with `AllPassed, `AllPassed -> `AllPassed | _ -> `SomeFailed in
  let result = ref `AllPassed in
  for i = 0 to Array.length testfiles - 1 do
    let file = testfiles.(i) in
    let res =
      if Sys.is_directory file then
        run_all (Array.map (fun x -> file ^ Filename.dir_sep ^ x) (Sys.readdir file))
      else if Filename.check_suffix file ".md" then
        run_file load_testcases_markdown file
      else if Filename.check_suffix file ".test" then
        run_file load_testcases file
      else
        `AllPassed in
    result := combine res !result
  done;
  !result


let () =
  match Sys.argv with
  | [| me |] -> Format.printf "Usage: %s <test files>\n" me; exit 1
  | _ ->
     match run_all (Array.sub Sys.argv 1 (Array.length Sys.argv - 1)) with
     | `SomeFailed -> Format.printf "Some tests failed\n%!"; exit 1
     | `AllPassed -> Format.printf "All tests passed\n%!"; exit 0
