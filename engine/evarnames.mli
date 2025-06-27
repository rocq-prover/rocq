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

(** Whether the [Generate Goal Names] option is enabled. *)
val generate_goal_names : unit -> bool

(** Creates a qualified name from a list of identifiers. *)
val of_list : Id.t list -> Id.t

(** Represents an evar name map. *)
type t

(** Returns an empty name map. *)
val empty : t

(** Adds a binding for the given undefined evar to the given basename.
    The absolute path is obtained using the parent of the evar. *)
val add : Id.t -> Evar.t -> ?parent:Evar.t -> t -> t

(** Adds a (potentially fresh) binding for the given undefined evar to the given
    basename by first checking for conflicts. *)
val add_fresh : Id.t -> Evar.t -> ?parent:Evar.t -> t -> t

(** Removes the name of the given evar.
    This indicates that the evar was defined, and therefore is no longer
    accessible by name. *)
val remove : Evar.t -> t -> t

(** Transfers the name of the first evar to the second. *)
val transfer_name : Evar.t -> Evar.t -> t -> t

(** Returns the qualified name associated to the evar, if any. *)
val name_of : Evar.t -> t -> Id.t option

(** Returns [true] if the evar has a name.
    Equivalent to [name_of ev <> None] but faster since it does not compute the
    fully qualified name of [ev]. *)
val has_name : Evar.t -> t -> bool

(** Returns [true] if the evar has a name that is unambiguous. *)
val has_unambiguous_name : Evar.t -> t -> bool

(** Resolves the given (partially) qualified name to an evar.
    If the name resolution failed, raises [Not_found]. *)
val resolve : Id.t -> t -> Evar.t
