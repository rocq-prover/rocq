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
open Declarations
open Mod_declarations
open Summary.Interp

(** This module defines the global environment of Rocq. The functions
   below are exactly the same as the ones in [Safe_typing], operating on
   that global environment. [add_*] functions perform name verification,
   i.e. check that the name given as argument match those provided by
   [Safe_typing]. *)

val safe_env : state:_ read -> Safe_typing.safe_environment
val env : state:_ read -> Environ.env

val universes : state:_ read -> UGraph.t
val qualities : state:_ read -> Sorts.QVar.Set.t
val elim_graph : state:_ read -> QGraph.t
val named_context_val : state:_ read -> Environ.named_context_val
val named_context : state:_ read -> Constr.named_context

(** {6 Enriching the global environment } *)

(** Changing the (im)predicativity of the system *)
val set_impredicative_set : bool -> state:readwrite -> unit

val set_indices_matter : bool -> state:readwrite -> unit
val set_typing_flags : typing_flags -> state:readwrite -> unit
val set_check_guarded : bool -> state:readwrite -> unit
val set_check_positive : bool -> state:readwrite -> unit
val set_check_universes : bool -> state:readwrite -> unit
val typing_flags : state:_ read -> typing_flags
val set_allow_sprop : bool -> state:readwrite -> unit
val sprop_allowed : state:_ read -> bool
val set_rewrite_rules_allowed : bool -> state:readwrite -> unit
val rewrite_rules_allowed : state:_ read -> bool

(** Variables, Local definitions, constants, inductive types *)

val push_named_assum : (Id.t * Constr.types) -> state:readwrite -> unit
val push_named_def   : (Id.t * Entries.section_def_entry) -> state:readwrite -> unit
val push_section_context : UVars.UContext.t -> state:readwrite -> unit

val export_private_constants :
  Safe_typing.private_constants ->
  state:readwrite ->
  Safe_typing.exported_private_constant list

val add_constant :
  ?typing_flags:typing_flags ->
  Id.t -> Entries.constant_entry ->
  state:readwrite -> Constant.t
val fill_opaque : Safe_typing.opaque_certificate -> state:readwrite -> unit
val add_rewrite_rules : Id.t -> rewrite_rules_body -> state:readwrite -> unit
val add_mind :
  ?typing_flags:typing_flags ->
  Id.t -> Entries.mutual_inductive_entry ->
  state:readwrite ->
  MutInd.t * IndTyping.NotPrimRecordReason.t option

(** Extra universe constraints *)
val add_constraints : Univ.Constraints.t -> state:readwrite -> unit

val push_context_set : Univ.ContextSet.t -> state:readwrite -> unit

(** Extra sort qualities *)
val push_qualities : Sorts.QVar.Set.t -> state:readwrite -> unit

(** Non-interactive modules and module types *)

val add_module :
  Id.t -> Entries.module_entry -> inline ->
  state:readwrite ->
    ModPath.t * Mod_subst.delta_resolver
val add_modtype :
  Id.t -> Entries.module_type_entry -> inline ->
  state:readwrite ->
  ModPath.t
val add_include :
  Entries.module_struct_entry -> bool -> inline ->
  state:readwrite ->
    Mod_subst.delta_resolver

(** Sections *)

val open_section : state:readwrite -> unit
(** [poly] is true when the section should be universe polymorphic *)

val close_section : Summary.Interp.frozen -> state:readwrite -> unit
(** Close the section and reset the global state to the one at the time when
    the section what opened. *)

val sections_are_opened : state:_ read -> bool

(** {6 Section management for discharge } *)

val section_segment_of_constant : Constant.t -> state:_ read -> Cooking.cooking_info
val section_segment_of_inductive: MutInd.t -> state:_ read -> Cooking.cooking_info
val section_segment_of_reference : GlobRef.t -> state:_ read -> Cooking.cooking_info

val section_instance : GlobRef.t -> state:_ read -> Constr.t array
val is_in_section : GlobRef.t -> state:_ read -> bool

(** [discharge_proj_repr p] discharges projection [p] if the associated record
    was defined in the current section. If that is not the case, it returns [p]
    unchanged. *)
val discharge_proj_repr : Projection.Repr.t -> state:_ read -> Projection.Repr.t

(** Interactive modules and module types *)

val start_module : Id.t -> state:readwrite -> ModPath.t
val start_modtype : Id.t -> state:readwrite -> ModPath.t

val end_module : Summary.Interp.frozen -> Id.t ->
  (Entries.module_struct_entry * inline) option ->
  state:readwrite ->
    ModPath.t * MBId.t list * Mod_subst.delta_resolver

val end_modtype : Summary.Interp.frozen -> Id.t -> state:readwrite ->
  ModPath.t * MBId.t list

val add_module_parameter :
  MBId.t -> Entries.module_struct_entry -> inline ->
  state:readwrite ->
  module_type_body

(** {6 Queries in the global environment } *)

val lookup_named     : variable -> state:_ read -> Constr.named_declaration
val lookup_constant  : Constant.t -> state:_ read -> constant_body
val lookup_inductive : inductive -> state:_ read ->
  mutual_inductive_body * one_inductive_body
val lookup_pinductive : Constr.pinductive -> state:_ read ->
  mutual_inductive_body * one_inductive_body
val lookup_mind      : MutInd.t -> state:_ read -> mutual_inductive_body
val lookup_module    : ModPath.t -> state:_ read -> module_body
val lookup_modtype   : ModPath.t -> state:_ read -> module_type_body
val exists_objlabel  : Id.t -> state:_ read -> bool

val constant_of_delta_kn : KerName.t -> state:_ read -> Constant.t
val mind_of_delta_kn : KerName.t -> state:_ read -> MutInd.t

type indirect_accessor = {
  access_proof : Opaqueproof.opaque -> Opaqueproof.opaque_proofterm option;
}

val force_proof : indirect_accessor -> Opaqueproof.opaque -> Opaqueproof.opaque_proofterm

val body_of_constant : indirect_accessor -> Constant.t -> state:_ read ->
  (Constr.constr * unit Opaqueproof.delayed_universes * UVars.AbstractContext.t) option
(** Returns the body of the constant if it has any, and the polymorphic context
    it lives in. For monomorphic constant, the latter is empty, and for
    polymorphic constants, the term contains De Bruijn universe variables that
    need to be instantiated. *)

val body_of_constant_body : indirect_accessor ->
  constant_body ->
    (Constr.constr * unit Opaqueproof.delayed_universes * UVars.AbstractContext.t) option
(** Same as {!body_of_constant} but on {!constant_body}. *)

(** {6 Compiled libraries } *)

val start_library : DirPath.t -> state:readwrite -> ModPath.t
val export : output_native_objects:bool -> DirPath.t -> state:_ read ->
  ModPath.t * Safe_typing.compiled_library * Vmlibrary.compiled_library * Nativelib.native_library
val import :
  Safe_typing.compiled_library -> Vmlibrary.on_disk -> Safe_typing.vodigest -> state:readwrite ->
  ModPath.t

(** {6 Misc } *)

(** Function to get an environment from the constants part of the global
 * environment and a given context. *)

val env_of_context : Environ.named_context_val -> state:_ read -> Environ.env

val is_joined_environment : state:_ read -> bool
val is_curmod_library : state:_ read -> bool

val is_polymorphic : GlobRef.t -> state:_ read -> bool
val is_template_polymorphic : GlobRef.t -> state:_ read -> bool
val is_type_in_type : GlobRef.t -> state:_ read -> bool

(** {6 Retroknowledge } *)

val register_inline : Constant.t -> state:readwrite -> unit
val register_inductive : inductive -> 'a CPrimitives.prim_ind -> state:readwrite -> unit

(** {6 Oracle } *)

val set_strategy : Conv_oracle.evaluable -> Conv_oracle.level -> state:readwrite -> unit

(** {6 Conversion settings } *)

val set_share_reduction : bool -> state:readwrite -> unit

val set_VM : bool -> state:readwrite -> unit
val set_native_compiler : bool -> state:readwrite -> unit

(* Modifies the global state, registering new universes *)

val current_modpath : state:_ read -> ModPath.t

val current_dirpath : state:_ read -> DirPath.t

val global_env_summary_tag : Safe_typing.safe_environment Summary.Dyn.tag

module Internal :
sig

val reset_safe_env : Safe_typing.safe_environment -> state:readwrite -> unit
(** Only use for manipulation of private constants *)

end
