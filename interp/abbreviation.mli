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
open Notationextern

(** Abbreviations. *)

(** Key in the map of abbreviations. *)
type key = Globnames.abbreviation constraint key = KerName.t

(** Interpretation of an abbreviation. *)
type interp = Notation_term.interpretation

(** Representation of an abbreviation. *)
type t

(** [interp a] gives the interpretation of abbreviation [a]. *)
val interp : t -> interp

(** [full_path a] gives the full path of abbreviation [a]. *)
val full_path : t -> Libnames.full_path

(** [enabled a] indicates whether the abbreviation [a] is enabled. *)
val enabled : t -> bool

(** [only_parsing a] indicates whether the abbreviation [a] is only used for
    parsing, and not for printing. *)
val only_parsing : t -> bool

(** [fold f acc] folds function [f] over the current abbreviation map, using
    [acc] as the initial accumulator value. *)
val fold : (key -> t -> 'a -> 'a) -> 'a -> 'a

(** [find_opt k] gives the abbreviation associated with the key [k] in the
    abbreviation map, if there is one. *)
val find_opt : key -> t option

val declare_abbreviation : local:bool ->
  Globnames.extended_global_reference UserWarn.with_qf option -> Id.t ->
  onlyparsing:bool -> interp -> unit

val search_abbreviation : key -> interp

val search_filtered_abbreviation : (interp -> 'a option) -> key -> 'a option

val import_abbreviation : int -> Libnames.full_path -> key -> unit

(** Activate (if on:true) or deactivate (if on:false) an abbreviation assumed to exist *)
val toggle_abbreviation : on:bool -> use:notation_use -> key -> unit

(** Activate (if on:true) or deactivate (if on:false) all abbreviations satisfying a criterion *)
val toggle_abbreviations : on:bool -> use:notation_use ->
  (Libnames.full_path -> interp -> bool) -> unit
