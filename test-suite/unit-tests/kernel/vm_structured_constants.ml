open OUnit
open Utest

let integer i =
  let env = Environ.empty_env in
  Vmlambda.lambda_of_constr ~share:true env (Genlambda.empty_evars env) (Constr.mkInt (Uint63.of_int i))

let block tag arg =
  match Vmlambda.as_value ~share:true tag [| arg |] with
  | Some value -> Vmlambda.get_lval value
  | None -> assert false

let sharing collect () =
  let arg = integer 42 in
  List.iter (fun tag ->
      let first = block tag arg in
      collect ();
      assert_bool "live VM block lost its representative" (first == block tag arg))
    [1; Obj.last_non_constant_constructor_tag; Obj.last_non_constant_constructor_tag + 1]

let resizing () =
  let args = Array.init 4096 integer in
  let blocks = Array.map (block 1) args in
  Gc.full_major ();
  Array.iteri (fun i first ->
      assert_bool "resizing lost a live VM block" (first == block 1 args.(i))) blocks

let distinct () =
  let arg = integer 42 in
  let first = block 1 arg in
  assert_bool "different tags were merged" (first != block 2 arg);
  assert_bool "different arguments were merged" (first != block 1 (integer 43))

let[@inline never] dead_block () =
  let weak = Weak.create 1 in
  Weak.set weak 0 (Some (block 1 (integer 8192)));
  weak

let collection () =
  let weak = dead_block () in
  Gc.full_major ();
  Gc.full_major ();
  assert_bool "the table retained an unreachable VM block" (not (Weak.check weak 0))

let tests = [
  mk_test "sharing survives minor collection" (TestCase (sharing Gc.minor));
  mk_test "sharing survives major collection" (TestCase (sharing Gc.full_major));
  mk_test "sharing survives compaction" (TestCase (sharing Gc.compact));
  mk_test "sharing survives resizing" (TestCase resizing);
  mk_test "distinct VM blocks stay distinct" (TestCase distinct);
  mk_test "unreachable VM blocks can be collected" (TestCase collection);
]

let () = run_tests __FILE__ (open_log_out_ch __FILE__) tests
