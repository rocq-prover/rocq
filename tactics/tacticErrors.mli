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
open EConstr
open Environ
open Evd
open Tactypes

(** Common exceptions raised by tactics. These exceptions are catched at
    toplevel and pretty-printed to the user. *)

(** {6 Raising exceptions.} *)

val intro_already_declared : ?loc:Loc.t -> Id.t -> 'a

val clear_dependency : ?loc:Loc.t -> env -> evar_map -> Id.t option ->
    Evarutil.clear_dependency_error -> GlobRef.t option -> 'a

val replacing_dependency : ?loc:Loc.t -> env -> evar_map -> Id.t ->
    Evarutil.clear_dependency_error -> GlobRef.t option -> 'a

val already_used : ?loc:Loc.t -> Id.t -> 'a

val used_twice : ?loc:Loc.t -> Id.t -> 'a

val variable_has_no_value : ?loc:Loc.t -> Id.t -> 'a

val convert_incompatible_types : ?loc:Loc.t -> env -> evar_map -> constr -> constr -> 'a

val convert_not_a_type : ?loc:Loc.t -> unit -> 'a

val not_convertible : ?loc:Loc.t -> unit -> 'a

val not_unfoldable : ?loc:Loc.t -> unit -> 'a

val no_quantified_hypothesis : ?loc:Loc.t -> quantified_hypothesis -> bool -> 'a

val cannot_find_instance : ?loc:Loc.t -> Id.t -> 'a

val nothing_to_rewrite : ?loc:Loc.t -> Id.t -> 'a

val ill_formed_elimination_type : ?loc:Loc.t -> unit -> 'a

val unable_to_apply_lemma : ?loc:Loc.t -> env -> evar_map -> constr -> constr -> 'a

val depends_on_body : ?loc:Loc.t -> Id.t list -> Id.Set.t -> Id.t option -> 'a

val not_right_number_constructors : ?loc:Loc.t -> int -> 'a

val not_enough_constructors : ?loc:Loc.t -> unit -> 'a

val constructors_numbered_from_one : ?loc:Loc.t -> unit -> 'a

val no_constructors : ?loc:Loc.t -> unit -> 'a

val unexpected_extra_pattern : ?loc:Loc.t -> int option ->
    delayed_open_constr intro_pattern_expr -> 'a

val cannot_find_inductive_argument : ?loc:Loc.t -> unit -> 'a

val one_intro_pattern_expected : ?loc:Loc.t -> unit -> 'a

val keep_and_clear_modifier_only_for_hypotheses : ?loc:Loc.t -> unit -> 'a

val fixpoint_on_non_inductive_type : ?loc:Loc.t -> unit -> 'a

val not_enough_products : ?loc:Loc.t -> unit -> 'a

val all_methods_in_coinductive_type : ?loc:Loc.t -> unit -> 'a

val replacement_ill_typed : ?loc:Loc.t -> exn -> 'a

val not_enough_premises : ?loc:Loc.t -> unit -> 'a

val need_dependent_product : ?loc:Loc.t -> unit -> 'a

(** {6 Internal use only.} *)

val clear_dependency_msg : env -> evar_map -> Names.Id.t option ->
    Evarutil.clear_dependency_error -> GlobRef.t option -> Pp.t

exception NotConvertible
exception DependsOnBody of Names.Id.t list * Names.Id.Set.t * Names.Id.t option
