(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Rocq package (encoded as a findlib package). *)
type t = {
  name : string;
  (** Package name (fully-qualified findlib package name). *)
  dir : string;
  (** Directory holding the package's Rocq files (first argument of "-Q"). *)
  logpath : string;
  (** Logical path associated to the directory (second argument of "-Q"). *)
}

(** [resolve ps] uses findlib to resolve the Rocq packages [ps], together with
    their transitive dependencies. A user error is triggered if a package does
    not exist, or if a dependency loop is found. *)
val resolve : string list -> t list
