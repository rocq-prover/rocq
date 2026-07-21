open OUnit
open Utest
open Names
open Mod_subst

let tests = ref []
let add_test name test = tests := mk_test name (TestCase test) :: !tests

let id = Id.of_string
let mp name = ModPath.MPfile (DirPath.make [id name])
let dot path name = ModPath.MPdot (path, id name)
let kn path name = KerName.make path (id name)

let assert_mp ?msg expected actual =
  assert_equal ?msg ~cmp:ModPath.equal ~printer:ModPath.to_string expected actual

let assert_kn ?msg expected actual =
  assert_equal ?msg ~cmp:KerName.equal ~printer:KerName.to_string expected actual

let assert_constant ?msg expected actual =
  let cmp x y =
    KerName.equal (Constant.user x) (Constant.user y) &&
    KerName.equal (Constant.canonical x) (Constant.canonical y)
  in
  assert_equal ?msg ~cmp ~printer:Constant.debug_to_string expected actual

let assert_mind ?msg expected actual =
  assert_equal ?msg ~cmp:MutInd.CanOrd.equal ~printer:MutInd.debug_to_string
    expected actual

let assert_ind ?msg expected actual =
  let printer (mind, index) =
    MutInd.debug_to_string mind ^ "," ^ string_of_int index
  in
  assert_equal ?msg ~cmp:Ind.CanOrd.equal ~printer expected actual

let assert_constructor ?msg expected actual =
  let printer ((mind, ind_index), cstr_index) =
    MutInd.debug_to_string mind ^ "," ^ string_of_int ind_index ^ "," ^
    string_of_int cstr_index
  in
  assert_equal ?msg ~cmp:Construct.CanOrd.equal ~printer expected actual

let assert_projection ?msg expected actual =
  assert_equal ?msg ~cmp:Projection.CanOrd.equal
    ~printer:Projection.debug_to_string
    expected actual

let assert_delta ?msg expected actual =
  assert_equal ?msg ~printer:(fun x -> x)
    (debug_string_of_delta expected) (debug_string_of_delta actual)

let empty_map from_ to_ = map_mp from_ to_ (empty_delta_resolver to_)

let sequential_mp subst1 subst2 path = subst_mp subst2 (subst_mp subst1 path)

let () = add_test "join preserves sequential module-path substitution" (fun () ->
  let a = mp "A" and b = mp "B" and c = mp "C" in
  let subst1 = empty_map a b in
  let subst2 = empty_map b c in
  let subst = join subst1 subst2 in
  List.iter (fun path ->
    assert_mp (sequential_mp subst1 subst2 path) (subst_mp subst path))
    [a; dot a "Inner"; dot (dot a "Inner") "Nested"];
  assert_mp c (subst_mp subst a);
  assert_mp (dot c "Inner") (subst_mp subst (dot a "Inner")))

let () = add_test "join handles empty and disjoint substitutions" (fun () ->
  let a = mp "A" and b = mp "B" and c = mp "C" and d = mp "D" in
  let subst1 = empty_map a b in
  let subst2 = empty_map c d in
  let joined = join subst1 subst2 in
  assert_mp b (subst_mp joined a);
  assert_mp d (subst_mp joined c);
  assert_mp b (subst_mp (join subst1 empty_subst) a);
  assert_mp b (subst_mp (join empty_subst subst1) a))

let () = add_test "join resolves overlapping prefixes in order" (fun () ->
  let a = mp "A" and b = mp "B" and c = mp "C" in
  let b_inner = dot b "Inner" in
  let subst1 = empty_map a b in
  let subst2 = empty_map b_inner c in
  let joined = join subst1 subst2 in
  assert_mp c (subst_mp joined (dot a "Inner"));
  assert_mp (dot c "Leaf") (subst_mp joined (dot (dot a "Inner") "Leaf")))

let () = add_test "join preserves unchanged module-path identity" (fun () ->
  let a = mp "A" and b = mp "B" in
  let untouched = dot (mp "Unchanged") "Inner" in
  let joined = join (empty_map a b) (empty_map b (mp "C")) in
  assert_bool "an unchanged path must retain pointer identity"
    (subst_mp joined untouched == untouched))

let () = add_test "join substitutes bound module paths sequentially" (fun () ->
  let a = mp "A" and b = mp "B" in
  let mbid = MBId.make DirPath.empty (id "Arg") in
  let subst1 = map_mbid mbid a (empty_delta_resolver a) in
  let subst2 = empty_map a b in
  let joined = join subst1 subst2 in
  assert_mp b (subst_mp joined (ModPath.MPbound mbid));
  assert_mp (dot b "Field")
    (subst_mp joined (dot (ModPath.MPbound mbid) "Field")))

let () = add_test "join preserves kernel-name and constant substitution" (fun () ->
  let a = mp "A" and b = mp "B" and c = mp "C" in
  let subst1 = empty_map a b in
  let subst2 = empty_map b c in
  let joined = join subst1 subst2 in
  let name = kn a "value" in
  assert_kn (subst_kn subst2 (subst_kn subst1 name)) (subst_kn joined name);
  let constant = Constant.make1 name in
  let sequential = subst_constant subst2 (subst_constant subst1 constant) in
  assert_constant sequential (subst_constant joined constant))

let () = add_test "join preserves inductive, projection, and term substitution" (fun () ->
  let a = mp "A" and b = mp "B" and c = mp "C" in
  let subst1 = empty_map a b in
  let subst2 = empty_map b c in
  let joined = join subst1 subst2 in
  let mind =
    MutInd.make (kn a "record") (kn (dot a "Canonical") "record")
  in
  let ind = mind, 0 in
  let cstr = ind, 1 in
  let projection =
    Projection.Repr.make ind ~proj_npars:0 ~proj_arg:0
    |> fun repr -> Projection.make repr false
  in
  let term = Constr.mkIndU (ind, UVars.Instance.empty) in
  assert_mind
    (subst_mind subst2 (subst_mind subst1 mind))
    (subst_mind joined mind);
  assert_ind
    (subst_ind subst2 (subst_ind subst1 ind))
    (subst_ind joined ind);
  assert_constructor
    (subst_constructor subst2 (subst_constructor subst1 cstr))
    (subst_constructor joined cstr);
  assert_projection
    (subst_proj subst2 (subst_proj subst1 projection))
    (subst_proj joined projection);
  assert_bool "joined term substitution differs from sequential application"
    (Constr.equal
      (subst_mps subst2 (subst_mps subst1 term))
      (subst_mps joined term)))

let () = add_test "join substitutes inline bodies after expansion" (fun () ->
  let a = mp "A" and b = mp "B" and c = mp "C" in
  let value_a = kn a "value" and value_b = kn b "value" in
  let body_b = Constant.make2 b (id "body") in
  let body = {
    UVars.univ_abstracted_value =
      Constr.mkConstU (body_b, UVars.Instance.empty);
    univ_abstracted_binder = UVars.AbstractContext.empty;
  } in
  let resolver1 =
    empty_delta_resolver b
    |> add_inline_delta_resolver value_b (0, Some body)
  in
  let subst1 = map_mp a b resolver1 in
  let subst2 = empty_map b c in
  let joined = join subst1 subst2 in
  let constant = Constant.make1 value_a in
  let _, joined_body = subst_con joined constant in
  let _, first_body = subst_con subst1 constant in
  let sequential_body =
    Option.map (UVars.map_univ_abstracted (subst_mps subst2)) first_body
  in
  match sequential_body, joined_body with
  | Some expected, Some actual ->
    assert_bool "joined inline body differs from sequential application"
      (Constr.equal expected.UVars.univ_abstracted_value
        actual.UVars.univ_abstracted_value)
  | None, None -> assert_failure "the inline hint was not exercised"
  | _ -> assert_failure "join changed whether the constant is inlined")

let () = add_test "resolver domain substitutions compose sequentially" (fun () ->
  let a = mp "A" and b = mp "B" and c = mp "C" in
  let resolver =
    empty_delta_resolver a
    |> add_mp_delta_resolver (dot a "Inner") (dot a "Canonical")
    |> add_kn_delta_resolver (kn a "value") (kn (dot a "Canonical") "value")
  in
  let expected =
    resolver
    |> subst_dom_delta_resolver a b
    |> subst_dom_delta_resolver b c
  in
  assert_delta expected (subst_dom_delta_resolver a c resolver))

let () = add_test "joined substitutions act sequentially on resolver codomains" (fun () ->
  let root = mp "Root" and a = mp "A" and b = mp "B" and c = mp "C" in
  let resolver =
    empty_delta_resolver root
    |> add_mp_delta_resolver (dot root "Inner") (dot a "Canonical")
    |> add_kn_delta_resolver (kn root "value") (kn a "value")
  in
  let subst1 = empty_map a b in
  let subst2 = empty_map b c in
  let expected =
    resolver
    |> subst_codom_delta_resolver subst1
    |> subst_codom_delta_resolver subst2
  in
  assert_delta expected (subst_codom_delta_resolver (join subst1 subst2) resolver))

let () = add_test "joined substitutions act sequentially on resolver domains and codomains" (fun () ->
  let a = mp "A" and b = mp "B" and c = mp "C" in
  let resolver =
    empty_delta_resolver a
    |> add_mp_delta_resolver (dot a "Inner") (dot a "Canonical")
    |> add_kn_delta_resolver (kn a "value") (kn (dot a "Canonical") "value")
  in
  let subst1 = empty_map a b in
  let subst2 = empty_map b c in
  let expected =
    resolver
    |> subst_dom_codom_delta_resolver subst1
    |> subst_dom_codom_delta_resolver subst2
  in
  assert_delta expected
    (subst_dom_codom_delta_resolver (join subst1 subst2) resolver))

let () = add_test "direct extensions preserve an already composed substitution" (fun () ->
  let a = mp "A" and b = mp "B" and c = mp "C" in
  let d = mp "D" and e = mp "E" in
  let composed = join (empty_map a b) (empty_map b c) in
  let extended = add_mp d e (empty_delta_resolver e) composed in
  assert_mp c (subst_mp extended a);
  assert_mp e (subst_mp extended d);
  let mbid = MBId.make DirPath.empty (id "Arg") in
  let extended = add_mbid mbid d (empty_delta_resolver d) composed in
  assert_mp c (subst_mp extended a);
  assert_mp d (subst_mp extended (ModPath.MPbound mbid)))

let () = add_test "joined substitutions survive marshal round trips" (fun () ->
  let a = mp "A" and b = mp "B" and c = mp "C" in
  let joined = join (empty_map a b) (empty_map b c) in
  let serialized = Marshal.to_string joined [] in
  let restored : substitution = Marshal.from_string serialized 0 in
  assert_mp c (subst_mp restored a);
  assert_mp (dot c "Inner") (subst_mp restored (dot a "Inner")))

let () = add_test "long join chains preserve sequential behavior" (fun () ->
  let rec build index current subst =
    if Int.equal index 10000 then current, subst
    else
      let next = mp ("M" ^ string_of_int (index + 1)) in
      build (index + 1) next (join subst (empty_map current next))
  in
  let start = mp "M0" in
  let expected, subst = build 0 start empty_subst in
  assert_mp expected (subst_mp subst start);
  assert_mp (dot expected "Field") (subst_mp subst (dot start "Field")))

let () = add_test "right-associated join chains preserve sequential behavior" (fun () ->
  let rec build index =
    if Int.equal index 256 then empty_subst
    else
      let current = mp ("R" ^ string_of_int index) in
      let next = mp ("R" ^ string_of_int (index + 1)) in
      join (empty_map current next) (build (index + 1))
  in
  let start = mp "R0" and expected = mp "R256" in
  let subst = build 0 in
  assert_mp expected (subst_mp subst start);
  assert_mp (dot expected "Field") (subst_mp subst (dot start "Field")))

let () = add_test "bounded normalization preserves inline resolver semantics" (fun () ->
  let first = mp "N0" and second = mp "N1" in
  let source_name = kn first "value" and mapped_name = kn second "value" in
  let body_constant = Constant.make2 second (id "body") in
  let body = {
    UVars.univ_abstracted_value =
      Constr.mkConstU (body_constant, UVars.Instance.empty);
    univ_abstracted_binder = UVars.AbstractContext.empty;
  } in
  let first_resolver =
    empty_delta_resolver second
    |> add_inline_delta_resolver mapped_name (0, Some body)
  in
  let rec extend index subst =
    if Int.equal index 65 then subst
    else
      let current = mp ("N" ^ string_of_int index) in
      let next = mp ("N" ^ string_of_int (index + 1)) in
      extend (index + 1) (join subst (empty_map current next))
  in
  let subst = extend 1 (map_mp first second first_resolver) in
  let expected_path = mp "N65" in
  let _, inline_body = subst_con subst (Constant.make1 source_name) in
  match inline_body with
  | None -> assert_failure "normalization discarded an inline resolver hint"
  | Some body ->
    let expected =
      Constr.mkConstU
        (Constant.make2 expected_path (id "body"), UVars.Instance.empty)
    in
    assert_bool "normalization did not substitute the inline body"
      (Constr.equal expected body.UVars.univ_abstracted_value))

let () = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
