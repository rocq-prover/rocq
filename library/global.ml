(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

(** We introduce here the global environment of the system,
    and we declare it as a synchronized table. *)

let global_env_summary_name = "Global environment"

module GlobalSafeEnv : sig

  val safe_env : state:_ Summary.Interp.read -> Safe_typing.safe_environment
  val set_safe_env : state:Summary.Interp.readwrite -> Safe_typing.safe_environment -> unit
  val is_joined_environment : state:_ Summary.Interp.read -> bool
  val is_curmod_library : state:_ Summary.Interp.read -> bool
  val global_env_summary_tag : Safe_typing.safe_environment Summary.Dyn.tag

end = struct

let Summary.{read = global_env; write = set_safe_env}, global_env_summary_tag =
  Summary.ref_tag ~name:global_env_summary_name Safe_typing.empty_environment

let set_safe_env ~state v = set_safe_env state v

let is_joined_environment ~state =
  Safe_typing.is_joined_environment (global_env state)

let is_curmod_library ~state =
  Safe_typing.is_curmod_library (global_env state)

let assert_not_synterp () =
  if !Flags.in_synterp_phase = Some true then
    CErrors.anomaly (
      Pp.strbrk"The global environment cannot be accessed during the syntactic interpretation phase.")

let safe_env ~state = assert_not_synterp(); global_env state

end

let global_env_summary_tag = GlobalSafeEnv.global_env_summary_tag

let safe_env = GlobalSafeEnv.safe_env
let is_joined_environment = GlobalSafeEnv.is_joined_environment
let is_curmod_library = GlobalSafeEnv.is_curmod_library

let env ~state = Safe_typing.env_of_safe_env (safe_env ~state)

(** Turn ops over the safe_environment state monad to ops on the global env *)

let prof f () =
  NewProfile.profile "kernel" f ()

let globalize0 f ~state = prof (fun () -> GlobalSafeEnv.set_safe_env ~state (f (safe_env ~state))) ()

let globalize f ~state =
  prof (fun () ->
      let res,env = f (safe_env ~state) in GlobalSafeEnv.set_safe_env ~state env; res)
    ()

let globalize0_with_summary fs f ~state =
  let env = prof (fun () -> f (safe_env ~state)) () in
  Summary.Interp.unfreeze_summaries fs;
  GlobalSafeEnv.set_safe_env ~state env

let globalize_with_summary fs f ~state =
  let res,env = prof (fun () -> f (safe_env ~state)) () in
  Summary.Interp.unfreeze_summaries fs;
  GlobalSafeEnv.set_safe_env ~state env;
  res

(** [Safe_typing] operations, now operating on the global environment *)

let i2l = Label.of_id

let push_named_assum a = globalize0 (Safe_typing.push_named_assum a)
let push_named_def d = globalize0 (Safe_typing.push_named_def d)
let push_section_context c = globalize0 (Safe_typing.push_section_context c)
let add_constraints c = globalize0 (Safe_typing.add_constraints c)
let push_context_set c = globalize0 (Safe_typing.push_context_set ~strict:true c)
let push_qualities c = globalize0 (Safe_typing.push_qualities c)

let set_impredicative_set c = globalize0 (Safe_typing.set_impredicative_set c)
let set_indices_matter b = globalize0 (Safe_typing.set_indices_matter b)
let set_typing_flags c = globalize0 (Safe_typing.set_typing_flags c)
let set_check_guarded c = globalize0 (Safe_typing.set_check_guarded c)
let set_check_positive c = globalize0 (Safe_typing.set_check_positive c)
let set_check_universes c = globalize0 (Safe_typing.set_check_universes c)
let typing_flags ~state = Environ.typing_flags (env ~state)
let set_allow_sprop b = globalize0 (Safe_typing.set_allow_sprop b)
let sprop_allowed ~state = Environ.sprop_allowed (env ~state)
let set_rewrite_rules_allowed b = globalize0 (Safe_typing.set_rewrite_rules_allowed b)
let rewrite_rules_allowed ~state = Environ.rewrite_rules_allowed (env ~state)
let export_private_constants cd = globalize (Safe_typing.export_private_constants cd)
let add_constant ?typing_flags id d = globalize (Safe_typing.add_constant ?typing_flags (i2l id) d)
let fill_opaque c = globalize0 (Safe_typing.fill_opaque c)
let add_rewrite_rules id c = globalize0 (Safe_typing.add_rewrite_rules (i2l id) c)
let add_mind ?typing_flags id mie = globalize (Safe_typing.add_mind ?typing_flags (i2l id) mie)
let add_modtype id me inl = globalize (Safe_typing.add_modtype (i2l id) me inl)
let add_module id me inl = globalize (Safe_typing.add_module (i2l id) me inl)
let add_include me ismod inl = globalize (Safe_typing.add_include me ismod inl)

let open_section = globalize0 Safe_typing.open_section
let close_section fs = globalize0_with_summary fs Safe_typing.close_section
let sections_are_opened ~state = Safe_typing.sections_are_opened (safe_env ~state)

let sections ~state = Safe_typing.sections_of_safe_env @@ safe_env ~state

let force_sections ~state = match sections ~state with
  | Some s -> s
  | None ->
    (* XXX should this be anomaly? *)
    CErrors.user_err Pp.(str "No open section.")

let section_segment_of_constant con ~state =
  Section.segment_of_constant con (force_sections ~state)

let section_segment_of_inductive kn ~state =
  Section.segment_of_inductive kn (force_sections ~state)

let section_segment_of_reference kn ~state = let open GlobRef in match kn with
| ConstRef c -> section_segment_of_constant c ~state
| IndRef (kn,_) | ConstructRef ((kn,_),_) ->
  section_segment_of_inductive kn ~state
| VarRef _ -> Cooking.empty_cooking_info

let is_in_section ref ~state = match sections ~state with
  | None -> false
  | Some sec ->
    Section.is_in_section (env ~state) ref sec

let section_instance ref ~state =
  Cooking.instance_of_cooking_info (section_segment_of_reference ref ~state)

let discharge_section_proj_repr p ~state =
  let ind = Projection.Repr.inductive p in
  let sec = section_segment_of_reference (GlobRef.IndRef ind) ~state in
  Cooking.discharge_proj_repr sec p

let discharge_proj_repr p ~state =
    if is_in_section (Names.GlobRef.IndRef (Names.Projection.Repr.inductive p)) ~state then
      discharge_section_proj_repr p ~state
    else
      p

let start_module id = globalize (Safe_typing.start_module (i2l id))
let start_modtype id = globalize (Safe_typing.start_modtype (i2l id))

let end_module fs id mtyo =
  globalize_with_summary fs (Safe_typing.end_module (i2l id) mtyo)

let end_modtype fs id =
  globalize_with_summary fs (Safe_typing.end_modtype (i2l id))

let add_module_parameter mbid mte inl =
  globalize (Safe_typing.add_module_parameter mbid mte inl)

(** Queries on the global environment *)

let universes ~state = Environ.universes (env ~state)
let qualities ~state = Environ.qualities (env ~state)
let named_context ~state = Environ.named_context (env ~state)
let named_context_val ~state = Environ.named_context_val (env ~state)

let lookup_named id ~state = Environ.lookup_named id (env ~state)
let lookup_constant kn ~state = Environ.lookup_constant kn (env ~state)
let lookup_inductive ind ~state = Inductive.lookup_mind_specif (env ~state) ind
let lookup_pinductive (ind,_) ~state = Inductive.lookup_mind_specif (env ~state) ind
let lookup_mind kn ~state = Environ.lookup_mind kn (env ~state)

let lookup_module mp ~state = Environ.lookup_module mp (env ~state)
let lookup_modtype kn ~state = Environ.lookup_modtype kn (env ~state)

let exists_objlabel id ~state = Safe_typing.exists_objlabel id (safe_env ~state)

type indirect_accessor = {
  access_proof : Opaqueproof.opaque -> Opaqueproof.opaque_proofterm option;
}

let force_proof access o = match access.access_proof o with
| None -> CErrors.user_err Pp.(str "Cannot access opaque delayed proof")
| Some (c, u) -> (c, u)

let body_of_constant_body access cb =
  let open Declarations in
  match cb.const_body with
  | Undef _ | Primitive _ | Symbol _ ->
     None
  | Def c ->
    let u = match cb.const_universes with
    | Monomorphic -> Opaqueproof.PrivateMonomorphic ()
    | Polymorphic auctx -> Opaqueproof.PrivatePolymorphic Univ.ContextSet.empty
    in
    Some (c, u, Declareops.constant_polymorphic_context cb)
  | OpaqueDef o ->
    let c, u = force_proof access o in
    Some (c, u, Declareops.constant_polymorphic_context cb)

let body_of_constant access cst ~state = body_of_constant_body access (lookup_constant cst ~state)

(** Operations on kernel names *)

let constant_of_delta_kn kn ~state =
  Safe_typing.constant_of_delta_kn_senv (safe_env ~state) kn

let mind_of_delta_kn kn ~state =
  Safe_typing.mind_of_delta_kn_senv (safe_env ~state) kn

(** Operations on libraries *)

let start_library dir = globalize (Safe_typing.start_library dir)
let export ~output_native_objects s ~state =
  Safe_typing.export ~output_native_objects (safe_env ~state) s
let import c t d = globalize (Safe_typing.import c t d)

(** Function to get an environment from the constants part of the global
    environment and a given context. *)

let env_of_context hyps ~state =
  Environ.reset_with_named_context hyps (env ~state)

let is_polymorphic r ~state =
  Environ.is_polymorphic (env ~state) r

let is_template_polymorphic r ~state =
  Environ.is_template_polymorphic (env ~state) r

let is_type_in_type r ~state =
  Environ.is_type_in_type (env ~state) r

let current_modpath ~state =
  Safe_typing.current_modpath (safe_env ~state)

let current_dirpath ~state =
  Safe_typing.current_dirpath (safe_env ~state)

let with_global f ~state =
  let (a, ctx) = f (env ~state) (current_dirpath ~state) in
  push_context_set ctx ~state; a

let register_inline c = globalize0 (Safe_typing.register_inline c)
let register_inductive c r = globalize0 (Safe_typing.register_inductive c r)

let set_strategy k l =
  globalize0 (Safe_typing.set_strategy k l)

let set_share_reduction b =
  globalize0 (Safe_typing.set_share_reduction b)

let set_VM b = globalize0 (Safe_typing.set_VM b)
let set_native_compiler b = globalize0 (Safe_typing.set_native_compiler b)

module Internal =
struct

let reset_safe_env = GlobalSafeEnv.set_safe_env

end
