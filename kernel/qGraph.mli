(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Sorts

(** {6 Graphs of quality elimination constraints. } *)

(* *********************************************** *)
(* "Raw" elimination table between constants.
    Used to specify the elimination rules between constant sorts. *)

module ElimTable : sig
  val eliminates_to : Quality.t -> Quality.t -> bool
end

(* ************************************************ *)

type t

type path_explanation

type explanation =
  | Path of path_explanation
  | Other of Pp.t

type quality_inconsistency =
  ((QVar.t -> Pp.t) option) * (ElimConstraint.kind * Quality.t * Quality.t * explanation option)

type elimination_error =
  | IllegalConstraint
  | CreatesForbiddenPath of Quality.t * Quality.t
  | QualityInconsistency of quality_inconsistency

exception EliminationError of elimination_error

exception AlreadyDeclared
val add_quality : Quality.t -> t -> t
(** Always call this function on a quality before trying to [enforce] or [check]
    a constraint or calling [eliminates_to].
    Forces [Type] to eliminate to this quality. *)

type constraint_source =
  | Internal
  | Rigid
  | Static

val merge_constraints : constraint_source -> ElimConstraints.t -> t -> t

val check_constraint : t -> ElimConstraint.t -> bool
val check_constraints : ElimConstraints.t -> t -> bool

val enforce_eliminates_to : constraint_source -> Quality.t -> Quality.t -> t -> t
(** Set the first quality to eliminate to the second one in the graph.

    If this constraint creates a cycle that violates the constraints,
    [QualityInconsistency] is raised.
    On an [Internal] enforcement, it also checks whether a path is created
    between two ground/global sorts.
    The [Rigid] [constraint_source] should be used for constraints entered by
    the user. It allows to create paths between ground/global sorts, but
    disables path creation between two ground sorts.
    No additional check is performed on a [Static] constraint. *)

val enforce_eq : Quality.t -> Quality.t -> t -> t
(** Set the first quality equal to the second one in the graph.
    If it's impossible, raise [QualityInconsistency]. *)

val initial_graph : t
(** Graph with the constant quality elimination constraints found in
    [Quality.Constants.eliminates_to]. *)

val eliminates_to : t -> Quality.t -> Quality.t -> bool
val eliminates_to_prop : t -> Quality.t -> bool
val sort_eliminates_to : t -> Sorts.t -> Sorts.t -> bool

val check_eq : t -> Quality.t -> Quality.t -> bool
val check_eq_sort : t -> Sorts.t -> Sorts.t -> bool

val domain : t -> Quality.Set.t
val qvar_domain : t -> QVar.Set.t

val is_empty : t -> bool

val explain_quality_inconsistency : (QVar.t -> Pp.t) -> quality_inconsistency -> Pp.t

val explain_elimination_error : (QVar.t -> Pp.t) -> elimination_error -> Pp.t

module Internal : sig
  val add_template_qvars : QVar.Set.t -> t -> t
  (** Set all the qvars in the set to eliminate to Prop.
      Do not use outside kernel inductive typechecking. *)
end
