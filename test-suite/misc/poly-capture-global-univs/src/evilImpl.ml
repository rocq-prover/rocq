open Names

let evil sum name name_f =
  let open Univ in
  let open UVars in
  let open Constr in
  let kind = Decls.(IsDefinition Definition) in
  let u = Level.var 0 in
  let tu = mkType (Universe.make u) in
  let te = Declare.definition_entry
      ~univs:(UState.Monomorphic_entry (Univ.ContextSet.singleton u), UnivNames.empty_binders) tu
  in
  let tc = Declare.declare_constant sum ~name ~kind (Declare.DefinitionEntry te) in
  let tc = mkConst tc in

  let fe = Declare.definition_entry
      ~univs:(UState.Polymorphic_entry (UContext.make {quals = [||]; univs= [|Anonymous|]} (Instance.of_array ([||],[|u|]),PConstraints.empty)), UnivNames.empty_binders)
      ~types:(Term.mkArrowR tc tu)
      (mkLambda (Context.nameR (Id.of_string "x"), tc, mkRel 1))
  in
  let _ : Constant.t = Declare.declare_constant sum ~name:name_f ~kind (Declare.DefinitionEntry fe) in
  ()
