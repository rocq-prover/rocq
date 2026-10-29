open Constr

let vm_normalize env ty =
  let sigma = Evd.from_env env in
  let sort = (Typeops.infer env ty).Environ.uj_type in
  let normal = Vnorm.cbv_vm env sigma
      (EConstr.of_constr ty) (EConstr.of_constr sort) in
  EConstr.to_constr sigma normal

let convert pb env source target =
  match Conversion.default_conv pb env source target with
  | Ok () -> Ok ()
  | Error () -> Error Pp.(str "the types are not cumulatively convertible")

(* Only the inferred source type is VM-normalized. The original target is
   passed unchanged to ordinary conversion, which may reduce it as needed. *)
let vm_lhs_check pb env source target =
  assert (pb = Conversion.CUMUL);
  convert pb env (vm_normalize env source) target

let prepare_vm env ty = Ok (vm_normalize env ty)

let vm_lhs = Unsafe_cast.{
  check = vm_lhs_check;
  prepare_source = Some prepare_vm;
  prepare_target = None;
}

let () = Unsafe_cast.register ~id:"test.vm-lhs" vm_lhs

(* A simple whole-target preparation hook. The separate mock below tests
   adapting #20503's evaluator interface. *)
let () = Unsafe_cast.register ~id:"test.vm-rhs" Unsafe_cast.{
  check = (fun pb env source target ->
    convert pb env source (vm_normalize env target));
  prepare_source = None;
  prepare_target = Some prepare_vm;
}

(* Mock only #20503's evaluator interface, not erasure or index traversal.
   The identity stub is deliberately sufficient: ordinary conversion performs
   any computation needed by the test. *)
let mock_erasure_evaluate :
    Environ.env -> Constr.t -> Constr.types -> (Constr.t, unit) result =
  fun _ term _ -> Ok term

let mock_erasure_target env target =
  let ty = (Typeops.infer env target).Environ.uj_type in
  match mock_erasure_evaluate env target ty with
  | Ok target -> Ok target
  | Error () -> Error Pp.(str "mock erasure evaluation failed")

let () = Unsafe_cast.register ~id:"test.erase" Unsafe_cast.{
  check = (fun pb env source target ->
    match mock_erasure_target env target with
    | Ok target -> convert pb env source target
    | Error message -> Error message);
  prepare_source = None;
  prepare_target = Some mock_erasure_target;
}

let () = Unsafe_cast.register ~id:"test.reject" Unsafe_cast.{
  check = (fun _ _ _ _ -> Error Pp.(str "rejected by the test checker"));
  prepare_source = None;
  prepare_target = None;
}

(* Deliberately unsound, to test that this really is a trusted extension and
   that even unconditional acceptance is visible to Print Assumptions. *)
let () = Unsafe_cast.register ~id:"test.accept" Unsafe_cast.{
  check = (fun _ _ _ _ -> Ok ());
  prepare_source = None;
  prepare_target = None;
}

(* Invoked only by Relevance.v, so the failing regression does not prevent
   the original tests from loading this plugin. Rejecting relevance-changing
   casts is the proposed policy; the probe checks the kernel independently
   of the surface-syntax rejection tests. *)
let () = Unsafe_cast.register ~id:"test.relevance-regression" Unsafe_cast.{
  check = (fun _ env _ _ ->
    let open Context.Rel.Declaration in
    let env = Environ.push_rel (LocalAssum (Context.anonR, mkSProp)) env in
    let irrelevant = Context.make_annot Names.Name.Anonymous Sorts.Irrelevant in
    let env = Environ.push_rel (LocalAssum (irrelevant, mkRel 1)) env in
    let strict_type = mkRel 2 and strict_proof = mkRel 1 in
    (* Positive controls ensure the local context and both kinds of operand
       are valid, and same-relevance unsafe casts are still accepted. *)
    let source_type = (Typeops.infer env mkProp).Environ.uj_type in
    ignore (Typeops.infer_type env strict_type);
    ignore (Typeops.infer env (mkCast (mkProp, UNSAFEcast "test.accept", source_type)));
    ignore (Typeops.infer env (mkCast (strict_proof, UNSAFEcast "test.accept", strict_type)));
    let casts = [
      "relevant-to-SProp", mkCast (mkProp, UNSAFEcast "test.accept", strict_type);
      "SProp-to-relevant", mkCast (strict_proof, UNSAFEcast "test.accept", mkProp);
    ] in
    let accepted = List.filter_map (fun (label, cast) ->
        try ignore (Typeops.infer env cast); Some label
        with e when CErrors.noncritical e -> None)
      casts in
    match accepted with
    | [] -> Ok ()
    | accepted -> Error Pp.(str "kernel accepted relevance-changing unsafe casts: " ++
        str (String.concat ", " accepted)));
  prepare_source = None;
  prepare_target = None;
}

let expect_error f =
  let failed = try f (); false with e when CErrors.noncritical e -> true in
  assert failed

let () =
  expect_error (fun () -> Unsafe_cast.register ~id:"test.vm-lhs" vm_lhs);
  expect_error (fun () -> Unsafe_cast.register ~id:"" vm_lhs);
  let env = Environ.empty_env in
  let ty = (Typeops.infer env mkProp).Environ.uj_type in
  (* Exercise the kernel directly, not just elaboration. *)
  ignore (Typeops.infer env (mkCast (mkProp, UNSAFEcast "test.vm-lhs", ty)));
  ignore (Typeops.infer env (mkCast (mkProp, UNSAFEcast "test.erase", ty)));
  expect_error (fun () ->
    ignore (Typeops.infer env (mkCast (mkProp, UNSAFEcast "test.erase", mkProp))));
  expect_error (fun () ->
    ignore (Typeops.infer env (mkCast (mkProp, UNSAFEcast "test.vm-lhs", mkProp))));
  expect_error (fun () ->
    ignore (Typeops.infer env (mkCast (mkProp, UNSAFEcast "test.missing", ty))));
  expect_error (fun () ->
    ignore (Typeops.infer env (mkCast (mkProp, UNSAFEcast "test.reject", ty))));
  assert (equal_cast_kind (UNSAFEcast "test.vm-lhs")
      (UNSAFEcast (String.concat "" ["test."; "vm-lhs"])));
  assert (not (equal_cast_kind (UNSAFEcast "test.vm-lhs") (UNSAFEcast "test.vm-rhs")));
  (* Sharing must not confuse cast identifiers or discard nested casts. *)
  let lhs = mkCast (mkProp, UNSAFEcast "test.vm-lhs", ty) in
  let rhs = mkCast (mkProp, UNSAFEcast "test.vm-rhs", ty) in
  let lhs' = mkCast (mkProp,
    UNSAFEcast (String.concat "" ["test."; "vm-lhs"]), ty) in
  let shared = HConstr.of_constr env (mkApp (lhs, [|rhs; lhs'|])) in
  let () = match HConstr.kind shared with
    | App (head, args) ->
      let tbl = HConstr.Tbl.create () in
      HConstr.Tbl.add tbl head ();
      assert (HConstr.Tbl.find_opt tbl args.(0) = None);
      assert (HConstr.Tbl.find_opt tbl args.(1) = Some ())
    | _ -> assert false
  in
  match kind (mkCast (lhs, UNSAFEcast "test.vm-rhs", ty)) with
  | Cast (c, UNSAFEcast "test.vm-rhs", _) -> assert (isCast c)
  | _ -> assert false
