open Names
open Constr
open Declarations
open Entries

let calls = ref 0
let accept_id = "checker-test.accept"
let reject_id = "checker-test.reject"
let convert_id = "checker-test.convert"
let abstract_id = "checker-test.abstract"
let missing_id = "checker-test.missing"

let () =
  Unsafe_cast.register ~id:accept_id Unsafe_cast.{
    check = (fun _ _ _ _ -> incr calls; Ok ());
    prepare_source = None;
    prepare_target = None;
  };
  Unsafe_cast.register ~id:reject_id Unsafe_cast.{
    check = (fun _ _ _ _ -> Error (Pp.str "rejected by checker test"));
    prepare_source = None;
    prepare_target = None;
  };
  Unsafe_cast.register ~id:convert_id Unsafe_cast.{
    check = (fun pb env source target ->
      incr calls;
      ignore (Typeops.infer_type env source);
      ignore (Typeops.infer_type env target);
      match Conversion.default_conv pb env source target with
      | Ok () -> Ok ()
      | Error () -> Error (Pp.str "incorrect callback types or universe environment"));
    prepare_source = None;
    prepare_target = None;
  };
  Unsafe_cast.register ~id:abstract_id Unsafe_cast.{
    check = (fun _ env source _ ->
      incr calls;
      ignore (Typeops.infer_type env source);
      let _, universes = Vars.sort_and_universes_of_constr source in
      if Univ.Level.Set.mem (Univ.Level.var 0) universes then Ok ()
      else Error (Pp.str "the original abstract template comparison was instantiated"));
    prepare_source = None;
    prepare_target = None;
  }

let dir = DirPath.make [Id.of_string "CheckerCastTest"]
let level = Univ.Level.make (Univ.UGlobal.make dir "test" 0)
let universe = Univ.Universe.make level
let env = Environ.push_context_set
    (Univ.Level.Set.singleton level, Univ.UnivConstraints.empty) Environ.empty_env
let abstract_context = UVars.AbstractContext.make
    UVars.{ quals = [||]; univs = [|Name (Id.of_string "u")|] }
    PConstraints.empty
let abstract_universe = Univ.Universe.make (Univ.Level.var 0)
let quality_context = UVars.AbstractContext.make
    UVars.{ quals = [|Name (Id.of_string "q")|]; univs = [|Name (Id.of_string "u")|] }
    PConstraints.empty
let abstract_quality = Sorts.Quality.QVar (Sorts.QVar.make_var 0)

let build ?(quality=Sorts.Quality.qtype) name universes universe ~record ~let_param =
  let sort = mkSort (Sorts.make quality universe) in
  let id = Id.of_string name in
  let mind = MutInd.make2 (ModPath.MPfile dir) id in
  let a = Context.make_annot (Name (Id.of_string "A")) Sorts.Relevant in
  let b = Context.make_annot (Name (Id.of_string "B")) Sorts.Relevant in
  let field = Context.make_annot (Name (Id.of_string "field")) Sorts.Relevant in
  let params = [Context.Rel.Declaration.LocalAssum (a, sort)] in
  let params = if let_param then
      Context.Rel.Declaration.LocalDef (b, mkRel 1, sort) :: params
    else params in
  let nparams = List.length params in
  let result = mkApp (mkRel (nparams + 1), [|mkRel nparams|]) in
  let constructor = if record then
      mkProd (field, mkRel 1, Vars.lift 1 result)
    else result in
  let entry = {
    mind_entry_record = if record then Some (Some [|Id.of_string "self"|]) else None;
    mind_entry_finite = Finite;
    mind_entry_params = params;
    mind_entry_inds = [{
      mind_entry_typename = id;
      mind_entry_arity = sort;
      mind_entry_consnames = [Id.of_string (name ^ "_constructor")];
      mind_entry_lc = [constructor];
    }];
    mind_entry_universes = universes;
    mind_entry_variance = None;
    mind_entry_private = None;
  } in
  let body, why_not_record = Indtypes.check_inductive env ~sec_univs:None mind entry in
  if Option.has_some why_not_record then failwith "could not build primitive record fixture";
  mind, body

let template = build "Template" (Template_ind_entry {
    uctx = abstract_context;
    default_univs = UVars.Instance.of_array ([||], [|level|]);
  }) abstract_universe ~record:false ~let_param:false
let monomorphic = build "Monomorphic" Monomorphic_ind_entry universe
    ~record:false ~let_param:false
let polymorphic = build "Polymorphic" (Polymorphic_ind_entry abstract_context)
    abstract_universe ~record:false ~let_param:false
let record = build "Record" Monomorphic_ind_entry universe ~record:true ~let_param:true
let polymorphic_record = build "PolymorphicRecord" (Polymorphic_ind_entry abstract_context)
    abstract_universe ~record:true ~let_param:false
let template_record = build "TemplateRecord" (Template_ind_entry {
    uctx = abstract_context;
    default_univs = UVars.Instance.of_array ([||], [|level|]);
  }) abstract_universe ~record:true ~let_param:false
let quality_polymorphic = build ~quality:abstract_quality "QualityPolymorphic"
    (Polymorphic_ind_entry quality_context) abstract_universe ~record:false ~let_param:false
let quality_template = build ~quality:abstract_quality "QualityTemplate" (Template_ind_entry {
    uctx = quality_context;
    default_univs = UVars.Instance.of_array ([|Sorts.Quality.qtype|], [|level|]);
  }) abstract_universe ~record:false ~let_param:false

let mutual =
  let id = Id.of_string "Mutual" in
  let mind = MutInd.make2 (ModPath.MPfile dir) id in
  let a = Context.make_annot (Name (Id.of_string "A")) Sorts.Relevant in
  let child = Context.make_annot (Name (Id.of_string "child")) Sorts.Relevant in
  let make_packet name self other = {
    mind_entry_typename = name;
    mind_entry_arity = mkType universe;
    mind_entry_consnames = [Id.of_string (Id.to_string name ^ "_constructor")];
    mind_entry_lc = [mkProd (child, mkApp (mkRel other, [|mkRel 1|]),
        mkApp (mkRel (self + 1), [|mkRel 2|]))];
  } in
  let entry = {
    mind_entry_record = None;
    mind_entry_finite = Finite;
    mind_entry_params = [Context.Rel.Declaration.LocalAssum (a, mkType universe)];
    mind_entry_inds = [make_packet id 3 2; make_packet (Id.of_string "Other") 2 3];
    mind_entry_universes = Monomorphic_ind_entry;
    mind_entry_variance = None;
    mind_entry_private = None;
  } in
  mind, fst (Indtypes.check_inductive env ~sec_univs:None mind entry)

let dependent_record =
  let id = Id.of_string "DependentRecord" in
  let mind = MutInd.make2 (ModPath.MPfile dir) id in
  let binder name = Context.make_annot (Name (Id.of_string name)) Sorts.Relevant in
  let entry = {
    mind_entry_record = Some (Some [|Id.of_string "self"|]);
    mind_entry_finite = Finite;
    mind_entry_params = [
      Context.Rel.Declaration.LocalAssum (binder "P",
        mkProd (Context.anonR, mkRel 1, mkType universe));
      Context.Rel.Declaration.LocalAssum (binder "A", mkType universe);
    ];
    mind_entry_inds = [{
      mind_entry_typename = id;
      mind_entry_arity = mkType universe;
      mind_entry_consnames = [Id.of_string "dependent_constructor"];
      mind_entry_lc = [mkProd (binder "x", mkRel 2,
          mkProd (binder "y", mkApp (mkRel 2, [|mkRel 1|]),
            mkApp (mkRel 5, [|mkRel 4; mkRel 3|])))];
    }];
    mind_entry_universes = Monomorphic_ind_entry;
    mind_entry_variance = None;
    mind_entry_private = None;
  } in
  mind, fst (Indtypes.check_inductive env ~sec_univs:None mind entry)

let cast id t = mkCast (t, UNSAFEcast id, mkSort Sorts.type1)
let first f = function [] -> failwith "empty fixture context" | x :: xs -> f x :: xs
let first_array f a = Array.mapi (fun i x -> if i = 0 then f x else x) a
let packet f body = { body with mind_packets = first_array f body.mind_packets }
let declaration id = Context.Rel.Declaration.map_type (cast id)

let placements = [
  "parameters", (fun id body ->
    { body with mind_params_ctxt = first (declaration id) body.mind_params_ctxt });
  "user arity", (fun id -> packet (fun p ->
    { p with mind_user_arity = cast id p.mind_user_arity }));
  "user constructor", (fun id -> packet (fun p ->
    { p with mind_user_lc = first_array (cast id) p.mind_user_lc }));
  "arity context", (fun id -> packet (fun p ->
    { p with mind_arity_ctxt = first (declaration id) p.mind_arity_ctxt }));
  "constructor context", (fun id -> packet (fun p ->
    { p with mind_nf_lc = first_array (fun (ctx, t) ->
        first (declaration id) ctx, t) p.mind_nf_lc }));
  "constructor result", (fun id -> packet (fun p ->
    { p with mind_nf_lc = first_array (fun (ctx, t) -> ctx, cast id t) p.mind_nf_lc }));
]

let check (mind, body) =
  ignore (Coq_checklib.CheckInductive.check_inductive env mind body None)

let expect_error message fixture =
  let error = try check fixture; None with
    | CErrors.UserError error -> Some (Pp.string_of_ppcmds error)
  in
  match error with
  | Some error when CString.string_contains ~where:error ~what:message -> ()
  | Some error -> failwith ("unexpected checker rejection: " ^ error)
  | None -> failwith ("checker accepted a cast expected to fail: " ^ message)

let test_placement ?(accept=accept_id) name place ((mind, body) as fixture) =
  check fixture;
  let before = !calls in
  check (mind, place accept body);
  if !calls = before then failwith ("checker skipped the accepting callback in " ^ name);
  expect_error "rejected by checker test" (mind, place reject_id body);
  expect_error ("Unsafe cast \"" ^ missing_id ^ "\" is not registered.")
    (mind, place missing_id body)

let () =
  List.iter (fun (name, place) ->
      List.iter (test_placement name place)
        [template; monomorphic; polymorphic; record; polymorphic_record; template_record;
         quality_polymorphic; quality_template; mutual; dependent_record])
    placements;
  let projection id = packet (fun p ->
      match p.mind_record with
      | PrimRecord r -> { p with mind_record = PrimRecord { r with tys = first_array (cast id) r.tys } }
      | NotRecord | FakeRecord -> failwith "expected primitive record") in
  List.iter (test_placement "projection type" projection)
    [record; polymorphic_record; template_record; dependent_record];
  test_placement "dependent projection type" (fun id -> packet (fun p ->
      match p.mind_record with
      | PrimRecord r -> { p with mind_record = PrimRecord { r with
          tys = Array.mapi (fun i t -> if i = 1 then cast id t else t) r.tys } }
      | NotRecord | FakeRecord -> failwith "expected dependent primitive record")) dependent_record;
  List.iter (fun (fixture, universe) ->
      let parameter id body =
        let wrap t = mkCast (t, UNSAFEcast id, mkType (Univ.Universe.super universe)) in
        { body with mind_params_ctxt = first (Context.Rel.Declaration.map_type wrap)
            body.mind_params_ctxt }
      in
      test_placement ~accept:convert_id "convertible parameter" parameter fixture)
    [template, abstract_universe; monomorphic, universe; polymorphic, abstract_universe;
     quality_polymorphic, abstract_universe; quality_template, abstract_universe];
  List.iter (test_placement ~accept:abstract_id "abstract template comparison"
      (fun id body -> { body with mind_params_ctxt =
          first (declaration id) body.mind_params_ctxt }))
    [template; quality_template];
  let mind, body = template in
  let unchecked = mind, { body with mind_typing_flags =
      { body.mind_typing_flags with check_universes = false } } in
  (* This comparison only succeeds when the original declaration's universe
     checking flag is also installed in the callback's environment. *)
  test_placement ~accept:convert_id "declaration typing flags" (fun id body ->
      { body with mind_params_ctxt = first (declaration id) body.mind_params_ctxt }) unchecked;
  let rec let_value id = function
    | [] -> failwith "expected a let-bound parameter"
    | Context.Rel.Declaration.LocalDef (na, b, t) :: ctx ->
      Context.Rel.Declaration.LocalDef (na, mkCast (b, UNSAFEcast id, t), t) :: ctx
    | d :: ctx -> d :: let_value id ctx
  in
  test_placement "parameter let value" (fun id body ->
      { body with mind_params_ctxt = let_value id body.mind_params_ctxt }) record;
  test_placement "arity let value" (fun id -> packet (fun p ->
      { p with mind_arity_ctxt = let_value id p.mind_arity_ctxt })) record;
  test_placement "constructor let value" (fun id -> packet (fun p ->
      { p with mind_nf_lc = first_array (fun (ctx, t) -> let_value id ctx, t) p.mind_nf_lc })) record;
  print_endline "Original inductive casts: accepting, rejecting, and missing handlers checked."
