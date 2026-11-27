open OUnit
open Utest

open Names
open Constr
open Declarations
open Entries
open Context

let id = Id.of_string
let annot n = make_annot (Name (id n)) Sorts.Relevant
let anon = make_annot Anonymous Sorts.Relevant
let empty_u = UVars.Instance.empty

let base_senv name =
  let senv = Safe_typing.empty_environment in
  let dp = DirPath.make [id name] in
  let _, senv = Safe_typing.start_library dp senv in
  senv

let c_False = mkProd (annot "P", mkProp, mkRel 1)
let c_True = mkProd (annot "P", mkProp, mkProd (anon, mkRel 1, mkRel 2))
let c_I = mkLambda (annot "P", mkProp, mkLambda (annot "h", mkRel 1, mkRel 1))

let reject_indexed_prim_record () =
  let senv = base_senv "IndexedPrimRecord" in
  let entry = {
    mind_entry_record = Some (Some [| id "R" |]);
    mind_entry_finite = BiFinite;
    mind_entry_params = [
      Rel.Declaration.LocalAssum (annot "A", mkProp);
    ];
    mind_entry_inds = [{
      mind_entry_typename = id "R";
      mind_entry_arity = mkProd (annot "B", mkProp, mkSort Sorts.type1);
      mind_entry_consnames = [id "mkR"];
      mind_entry_lc = [
        mkProd (annot "proj0", mkRel 1, mkApp (mkRel 3, [| mkRel 2; c_False |]))
      ];
    }];
    mind_entry_universes = Monomorphic_ind_entry;
    mind_entry_variance = None;
    mind_entry_private = None;
  } in
  let rejected =
    match Safe_typing.add_mind (id "R") entry senv with
    | _ -> false
    | exception Type_errors.InductiveError (_, Type_errors.BadEntry) -> true
  in
  assert_bool "indexed PrimRecord should be rejected with BadEntry" rejected

let reject_letin_arity_prim_record () =
  let senv = base_senv "LetInArityPrimRecord" in
  let entry = {
    mind_entry_record = Some (Some [| id "R" |]);
    mind_entry_finite = BiFinite;
    mind_entry_params = [
      Rel.Declaration.LocalAssum (annot "A", mkProp);
    ];
    mind_entry_inds = [{
      mind_entry_typename = id "R";
      mind_entry_arity = mkLetIn (annot "B", mkProp, mkSort Sorts.type1, mkSort Sorts.type1);
      mind_entry_consnames = [id "mkR"];
      mind_entry_lc = [
        mkProd (annot "proj0", mkRel 1, mkApp (mkRel 3, [| mkRel 2 |]))
      ];
    }];
    mind_entry_universes = Monomorphic_ind_entry;
    mind_entry_variance = None;
    mind_entry_private = None;
  } in
  let rejected =
    match Safe_typing.add_mind (id "R") entry senv with
    | _ -> false
    | exception Type_errors.InductiveError (_, Type_errors.BadEntry) -> true
  in
  assert_bool "PrimRecord with let-in in arity should be rejected with BadEntry" rejected

let accept_non_indexed_prim_record () =
  let senv = base_senv "NonIndexedPrimRecord" in
  let (mind_R, _), senv =
    Safe_typing.add_mind (id "Box") {
      mind_entry_record = Some (Some [| id "Box" |]);
      mind_entry_finite = BiFinite;
      mind_entry_params = [
        Rel.Declaration.LocalAssum (annot "A", mkProp);
      ];
      mind_entry_inds = [{
        mind_entry_typename = id "Box";
        mind_entry_arity = mkSort Sorts.type1;
        mind_entry_consnames = [id "mkBox"];
        mind_entry_lc = [
          mkProd (annot "proj0", mkRel 1, mkApp (mkRel 3, [| mkRel 2 |]))
        ];
      }];
      mind_entry_universes = Monomorphic_ind_entry;
      mind_entry_variance = None;
      mind_entry_private = None;
    } senv
  in
  let mib = Environ.lookup_mind mind_R (Safe_typing.env_of_safe_env senv) in
  let is_prim = match mib.mind_packets.(0).mind_record with
    | PrimRecord _ -> true
    | NotRecord | FakeRecord -> false
  in
  assert_bool "non-indexed PrimRecord should remain PrimRecord" is_prim;
  let r_ind = (mind_R, 0) in
  let r_val = mkApp (mkConstructU ((r_ind, 1), empty_u), [| c_True; c_I |]) in
  let proj0 = Projection.make (Projection.Repr.make r_ind ~proj_npars:1 ~proj_arg:0) false in
  let _, _ =
    Safe_typing.add_constant (id "ok")
      (DefinitionEntry {
        definition_entry_body = mkProj (proj0, Sorts.Relevant, r_val);
        definition_entry_secctx = None;
        definition_entry_type = Some c_True;
        definition_entry_universes = Monomorphic_entry;
        definition_entry_inline_code = false;
      })
      senv
  in
  ()

let tests = [
  mk_test "reject indexed PrimRecord" (TestCase reject_indexed_prim_record);
  mk_test "reject let-in arity PrimRecord" (TestCase reject_letin_arity_prim_record);
  mk_test "accept non-indexed PrimRecord" (TestCase accept_non_indexed_prim_record);
]

let () = run_tests __FILE__ (open_log_out_ch __FILE__) tests
