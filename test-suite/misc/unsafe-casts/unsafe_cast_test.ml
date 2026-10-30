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

(* Invoked only by Relevance.v. Check the kernel independently of the
   surface-syntax rejection tests, including its public incremental API. *)
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
    let rejects f =
      try f (); false with
      | CErrors.UserError message ->
        let message = Pp.string_of_ppcmds message in
        if CString.string_contains ~where:message ~what:"cannot change relevance" then true
        else CErrors.user_err (Pp.str ("unexpected rejection: " ^ message))
    in
    let accepted = List.concat_map (fun (label, cast) ->
        let full = if rejects (fun () -> ignore (Typeops.infer env cast))
          then [] else [label] in
        let c, k, t = destCast cast in
        let cj = Typeops.infer env c and tj = Typeops.infer_type env t in
        let incremental = if rejects (fun () -> Typeops.check_cast env cj k tj)
          then [] else [label ^ " (check_cast)"] in
        full @ incremental)
      casts in
    match accepted with
    | [] -> Ok ()
    | accepted -> Error Pp.(str "kernel accepted relevance-changing unsafe casts: " ++
        str (String.concat ", " accepted)));
  prepare_source = None;
  prepare_target = None;
}

(* Inspect the declarations and compound terms built in Relevance.v, without
   relying on successful surface elaboration to validate cached metadata. *)
let () = Unsafe_cast.register ~id:"test.relevance-metadata" Unsafe_cast.{
  check = (fun _ env _ _ ->
    let lookup name = match Nametab.locate (Libnames.qualid_of_string name) with
      | Names.GlobRef.ConstRef c -> Environ.lookup_constant c env
      | _ -> assert false
    in
    let assert_relevance label expected actual =
      if not (Sorts.relevance_equal expected actual) then
        CErrors.user_err Pp.(str "incorrect relevance for " ++ str label)
    in
    List.iter (fun (name, expected) ->
        let cb = lookup name in
        let ty = Typeops.infer_type env cb.Declarations.const_type in
        assert_relevance (name ^ " (type)") expected (Sorts.relevance_of_sort ty.Environ.utj_type);
        assert_relevance (name ^ " (metadata)") expected cb.Declarations.const_relevance)
      ["relevance_indirect", Sorts.Irrelevant;
       "relevance_inferred", Sorts.Irrelevant;
       "relevance_relevant", Sorts.Relevant;
       "relevance_fun_indirect", Sorts.Irrelevant];
    List.iter (fun name ->
        let local = Names.Id.of_string name in
        if Environ.mem_named local env then begin
          let decl = Environ.lookup_named local env in
          let ty = Typeops.infer_type env (Context.Named.Declaration.get_type decl) in
          assert_relevance (name ^ " (section local metadata)")
            (Sorts.relevance_of_sort ty.Environ.utj_type)
            (Context.Named.Declaration.get_relevance decl)
        end)
      ["p"; "inferred_p"];
    let body name = match (lookup name).Declarations.const_body with
      | Declarations.Def c -> c
      | _ -> assert false
    in
    let zero = body "relevance_indirect" in
    let proof = body "relevance_relevant" in
    let nat = (Typeops.infer env zero).Environ.uj_type in
    let strict = (Typeops.infer env proof).Environ.uj_type in
    let strict_type = mkCast (nat, UNSAFEcast "test.accept", mkSProp) in
    let relevant_type = mkCast (strict, UNSAFEcast "test.accept", mkSet) in
    let into_strict = mkCast (zero, DEFAULTcast, strict_type) in
    let into_relevant = mkCast (proof, DEFAULTcast, relevant_type) in
    let lambda = mkLambda (Context.anonR, nat, Vars.lift 1 into_strict) in
    let ordinary_function = mkCast (mkLambda (Context.anonR, nat, Vars.lift 1 zero),
        DEFAULTcast, mkProd (Context.anonR, nat, Vars.lift 1 strict_type)) in
    let irrelevant = Context.make_annot Names.Name.Anonymous Sorts.Irrelevant in
    let terms = [
      "ordinary cast into SProp", into_strict, Sorts.Irrelevant;
      "ordinary cast out of SProp", into_relevant, Sorts.Relevant;
      "lambda", lambda, Sorts.Irrelevant;
      "application", mkApp (ordinary_function, [|zero|]), Sorts.Irrelevant;
      "let", mkLetIn (irrelevant, into_strict, strict_type, mkRel 1), Sorts.Irrelevant;
      "cast under a binder", mkLambda (irrelevant, strict,
        mkCast (mkRel 1, DEFAULTcast, Vars.lift 1 relevant_type)), Sorts.Relevant;
    ] in
    let sigma = Evd.from_env env in
    List.iter (fun (label, term, expected) ->
        let j = Typeops.infer env term in
        let tj = Typeops.infer_type env j.Environ.uj_type in
        assert_relevance (label ^ " (kernel type)") expected
          (Sorts.relevance_of_sort tj.Environ.utj_type);
        assert_relevance (label ^ " (kernel relevance)") expected
          (Relevanceops.relevance_of_term env term);
        let term = EConstr.of_constr term in
        assert_relevance (label ^ " (retyping)") expected
          (EConstr.ERelevance.kind sigma (Retyping.relevance_of_term env sigma term));
        let ty = Retyping.get_type_of env sigma term in
        assert_relevance (label ^ " (retyped type)") expected
          (EConstr.ERelevance.kind sigma (Retyping.relevance_of_type env sigma ty)))
      terms;
    Ok ());
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
