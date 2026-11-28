open OUnit
open Utest

let tests = ref []
let add_test name test = tests := mk_test name (TestCase test) :: !tests

let a, _ = CDebug.create_full ~name:"utest-a" ()
let b, _ = CDebug.create_full ~name:"utest-b" ()

let has_flag s flag = List.mem flag (String.split_on_char ',' s)

let reset () =
  CDebug.set_override "all" None;
  CDebug.set_override "backtrace" None;
  CDebug.set_override "utest-a" None;
  CDebug.set_override "utest-b" None;
  CDebug.set_flags "-all"

let test_component () =
  reset ();
  CDebug.set_override "utest-a" (Some true);
  assert_equal true (CDebug.get_flag a);
  assert_equal false (CDebug.get_flag b);
  (* the flags set by the commands ignore the override *)
  assert_bool "get_flags ignores the override" (has_flag (CDebug.get_flags ()) "-utest-a");
  (* and keep changing while the component is overridden *)
  CDebug.set_flags "-utest-a,utest-b";
  assert_equal true (CDebug.get_flag a);
  assert_equal true (CDebug.get_flag b);
  CDebug.set_override "utest-a" None;
  assert_equal false (CDebug.get_flag a);
  assert_equal true (CDebug.get_flag b);
  reset ()

let test_all () =
  reset ();
  CDebug.set_flags "utest-b";
  CDebug.set_override "utest-a" (Some true);
  CDebug.set_override "all" (Some false);
  (* "all" applies to the components without an override of their own *)
  assert_equal true (CDebug.get_flag a);
  assert_equal false (CDebug.get_flag b);
  assert_equal (Some false) (List.assoc_opt "all" (CDebug.get_flag_values ()));
  assert_equal (Some false) (List.assoc_opt "utest-b" (CDebug.get_flag_values ()));
  assert_bool "get_flags ignores the override" (has_flag (CDebug.get_flags ()) "utest-b");
  CDebug.set_override "all" None;
  assert_equal true (CDebug.get_flag b);
  reset ()

let test_backtrace () =
  reset ();
  let initial = Printexc.backtrace_status () in
  CDebug.set_flags "-backtrace";
  CDebug.set_override "backtrace" (Some true);
  assert_equal true (Printexc.backtrace_status ());
  assert_bool "get_flags ignores the override" (has_flag (CDebug.get_flags ()) "-backtrace");
  (* the setting of the commands is kept while overridden *)
  CDebug.set_flags "backtrace";
  CDebug.set_override "backtrace" (Some false);
  assert_equal false (Printexc.backtrace_status ());
  assert_bool "the setting is kept" (has_flag (CDebug.get_flags ()) "backtrace");
  CDebug.set_override "backtrace" None;
  assert_equal true (Printexc.backtrace_status ());
  reset ();
  Printexc.record_backtrace initial

let test_unknown () =
  let fails = try CDebug.set_override "utest-none" (Some true); false
    with CErrors.UserError _ -> true in
  assert_bool "unknown component" fails;
  assert_equal None (CDebug.get_override "utest-none")

let () = add_test "override a component" test_component
let () = add_test "override all" test_all
let () = add_test "override backtrace" test_backtrace
let () = add_test "override an unknown component" test_unknown

let () = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
