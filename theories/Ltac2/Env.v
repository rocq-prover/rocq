(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Ltac2 Require Import Init Std TransparentState.

Ltac2 @ external get : ident list -> Std.reference option := "rocq-runtime.plugins.ltac2" "env_get".
(** Returns the global reference corresponding to the absolute name given as
    argument if it exists. *)

Ltac2 @ external expand : ident list -> Std.reference list := "rocq-runtime.plugins.ltac2" "env_expand".
(** Returns the list of all global references whose absolute name contains
    the argument list as a suffix. *)

Ltac2 @ external path : Std.reference -> ident list := "rocq-runtime.plugins.ltac2" "env_path".
(** Returns the absolute name of the given reference. Panics if the reference
    does not exist. *)

Ltac2 @ external instantiate : Std.reference -> constr := "rocq-runtime.plugins.ltac2" "env_instantiate".
(** Returns a fresh instance of the corresponding reference, in particular
    generating fresh universe variables and constraints when this reference is
    universe-polymorphic. *)

Module Assumption.
(** Assumption analysis (as used by Print Assumptions) *)

  Ltac2 Type t.
  (** Opaque type representing an assumption (axiom, opaque constant, etc.) *)

  Ltac2 @external reference : t -> Std.reference :=
    "rocq-runtime.plugins.ltac2" "env_assumption_reference".
  (** Get the reference associated with an assumption *)

  Ltac2 @external is_axiom : t -> bool :=
    "rocq-runtime.plugins.ltac2" "env_assumption_is_axiom".
  (** Returns true if the assumption is an axiom (constant without body) *)

  Ltac2 @external is_opaque : t -> bool :=
    "rocq-runtime.plugins.ltac2" "env_assumption_is_opaque".
  (** Returns true if the assumption is an opaque constant *)

  Ltac2 @external is_transparent : t -> bool :=
    "rocq-runtime.plugins.ltac2" "env_assumption_is_transparent".
  (** Returns true if the assumption is a transparent constant *)

  Ltac2 @external assumes_positive : t -> bool :=
    "rocq-runtime.plugins.ltac2" "env_assumption_assumes_positive".
  (** Returns true if the assumption relies on a positivity assumption *)

  Ltac2 @external assumes_guarded : t -> bool :=
    "rocq-runtime.plugins.ltac2" "env_assumption_assumes_guarded".
  (** Returns true if the assumption relies on a guardedness assumption *)

  Ltac2 @external assumes_type_in_type : t -> bool :=
    "rocq-runtime.plugins.ltac2" "env_assumption_assumes_type_in_type".
  (** Returns true if the assumption relies on Type-in-Type *)

  Ltac2 @external assumes_uip : t -> bool :=
    "rocq-runtime.plugins.ltac2" "env_assumption_assumes_uip".
  (** Returns true if the assumption relies on definitional UIP *)
End Assumption.

Ltac2 @external assumptions : bool -> bool -> TransparentState.t -> Std.reference list -> (Assumption.t * constr) list :=
  "rocq-runtime.plugins.ltac2" "env_assumptions".
(** Returns the list of assumptions that a list of references depend on.
    The first bool enables including opaque constants.
    The second bool enables including transparent constants.
    The transparent_state controls which constants are considered transparent. *)
