(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Named, explicitly trusted extensions of cast checking. Only the identifier
    is stored in terms; callbacks must be registered in every checking process.
    Merely registering a handler does not taint declarations. *)

type type_transform =
  Environ.env -> Constr.types -> (Constr.types, Pp.t) result

type handler = {
  check : Conversion.conv_pb -> Environ.env ->
    Constr.types -> Constr.types -> (unit, Pp.t) result;
  (** [check pb env source target] decides the comparison itself, including any
      calls to conversion. Cast checking always supplies [CUMUL]. The operand
      and the original target have already been typechecked by the kernel.
      Acceptance is trusted, even if the types are not ordinarily convertible.
      Checks must be deterministic and respect the kernel's context-sensitive
      term sharing: unrelated local declarations must not affect their result. *)

  prepare_source : type_transform option;
  prepare_target : type_transform option;
  (** Optional elaboration aids. When either is present, ordinary unification
      of the prepared types is used to infer evars and universe constraints
      before calling [check] on the original types. A transformation is called
      only with an evar-free input and local environment. The kernel does not
      use these aids: it independently invokes [check]. *)
}

val register : id:string -> handler -> unit
(** Register a stable, namespaced identifier. Empty and duplicate identifiers
    are rejected; handlers cannot be replaced or removed. Registration should
    happen during plugin initialization, including in proof workers. *)

val find : string -> handler
(** Fail if the identifier is not registered. *)

val check : string -> Conversion.conv_pb -> Environ.env ->
  Constr.types -> Constr.types -> unit
(** Run the registered check, reporting a rejection as a user error. *)

val transform : string -> type_transform -> Environ.env ->
  Constr.types -> Constr.types
(** Run an elaboration aid, reporting its error with the cast identifier. *)
