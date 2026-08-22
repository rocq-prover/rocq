open OUnit
open Utest

let tests = ref []
let add_test name test = tests := mk_test name (TestCase test) :: !tests

let parse ?(init=Coqargs.default) args =
  fst (Coqargs.parse_args ~init args)

let first_args =
  [ "-I"; "ml-a"
  ; "-R"; "."; "Test"
  ; "-load-vernac-source"; "first"
  ; "-set"; "Printing Depth=10"
  ; "-package"; "package-a"
  ]

let second_args =
  [ "-I"; "ml-b"
  ; "-R"; "_build/default"; "Test"
  ; "-load-vernac-source"; "second"
  ; "-unset"; "Printing Depth"
  ; "-package"; "package-b"
  ]

let test_compositional () =
  let one_pass = parse (first_args @ second_args) in
  let split = parse ~init:(parse first_args) second_args in
  assert_equal one_pass split

let () = add_test "one-pass and incremental parsing agree" test_compositional

let test_empty_parse_identity () =
  let opts = parse (first_args @ second_args) in
  assert_equal opts (parse ~init:opts [])

let () = add_test "empty incremental parse preserves init" test_empty_parse_identity

let test_normalized_order () =
  let opts = parse (first_args @ second_args) in
  let expected_vo_includes : Coqargs.vo_path list =
    [ { implicit = true; unix_path = "."; rocq_path = "Test" }
    ; { implicit = true; unix_path = "_build/default"; rocq_path = "Test" }
    ]
  in
  assert_equal ["ml-a"; "ml-b"] opts.pre.ml_includes;
  assert_equal expected_vo_includes opts.pre.vo_includes;
  assert_equal ["package-a"; "package-b"] opts.pre.packages;
  assert_equal ["first.v"; "second.v"] opts.pre.load_vernacular_list

let () = add_test "ordered options are returned in declaration order" test_normalized_order

let test_packages_are_not_resolved_during_parsing () =
  let opts = parse ["-package"; "a-package-that-does-not-exist"] in
  assert_equal ["a-package-that-does-not-exist"] opts.pre.packages;
  assert_equal [] opts.pre.vo_includes

let () = add_test "package resolution is deferred" test_packages_are_not_resolved_during_parsing

let () = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
