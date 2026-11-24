open OUnit
open Utest
open Goptions

let tests = ref []
let add_test name test = tests := mk_test name (TestCase test) :: !tests

let key = ["Utest"; "Override"]
let { get } = declare_bool_option_and_ref ~key ~value:false ()

(* an option whose code asks for the override itself *)
let raw_key = ["Utest"; "Override"; "Raw"]
let raw = ref false
let () =
  declare_option ~overridable:true ~kind:BoolKind
    { optstage = Summary.Stage.Interp; optdepr = None; optkey = raw_key;
      optread = (fun () -> !raw); optwrite = (fun b -> raw := b) }

let not_overridable_key = ["Utest"; "Not"; "Overridable"]
let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp; optdepr = None; optkey = not_overridable_key;
      optread = (fun () -> false); optwrite = (fun _ -> ()) }

let nat_key = ["Utest"; "Override"; "Nat"]
let { get = get_nat } = declare_nat_option_and_ref ~key:nat_key ~value:2 ()

let value key = match get_option_value key with
  | Some read -> read ()
  | None -> assert false

let fails f = try f (); false with CErrors.UserError _ -> true

let test_getter () =
  set_option_override key (Some (BoolValue true));
  assert_equal true (get ());
  assert_equal (Some (BoolValue true)) (get_option_override key);
  (* the value set by the commands *)
  assert_equal (BoolValue false) (value key);
  set_option_override key None;
  assert_equal false (get ());
  assert_equal None (get_option_override key)

let test_summary () =
  (* the summary saves the values set by the commands, not the overrides *)
  set_option_override key (Some (BoolValue true));
  let st = Summary.Interp.freeze_summaries () in
  set_option_override key None;
  Summary.Interp.unfreeze_summaries st;
  assert_equal false (get ());
  (* restoring a state keeps the override *)
  set_option_override key (Some (BoolValue true));
  Summary.Interp.unfreeze_summaries st;
  assert_equal true (get ());
  set_option_override key None

let test_raw () =
  raw := false;
  let st0 = Summary.Interp.freeze_summaries () in
  set_option_override raw_key (Some (BoolValue true));
  (* what a [Set] does while the option is overridden *)
  raw := true;
  let st1 = Summary.Interp.freeze_summaries () in
  Summary.Interp.unfreeze_summaries st0;
  assert_equal false !raw;
  Summary.Interp.unfreeze_summaries st1;
  assert_equal true !raw;
  assert_equal (Some (BoolValue true)) (get_option_override raw_key);
  set_option_override raw_key None;
  Summary.Interp.unfreeze_summaries st0

let test_errors () =
  assert_bool "not overridable"
    (fails (fun () -> set_option_override not_overridable_key (Some (BoolValue true))));
  assert_bool "unknown option"
    (fails (fun () -> set_option_override ["Utest"; "Unknown"] (Some (BoolValue true))));
  assert_bool "bad type"
    (fails (fun () -> set_option_override key (Some (IntValue (Some 1)))));
  (* the value is checked when the override is set *)
  assert_bool "negative value"
    (fails (fun () -> set_option_override nat_key (Some (IntValue (Some (-1))))));
  assert_equal None (get_option_override nat_key);
  assert_equal 2 (get_nat ());
  set_option_override nat_key (Some (IntValue (Some 5)));
  assert_equal 5 (get_nat ());
  set_option_override nat_key None;
  assert_equal 2 (get_nat ())

let () = add_test "getters return the override" test_getter
let () = add_test "the summary ignores the overrides" test_summary
let () = add_test "overridable options keep their values in the summary" test_raw
let () = add_test "errors" test_errors

let () = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
