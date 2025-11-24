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

(** Abbreviations *)

(** Representation of the data associated to an abbreviation. *)
type data

(** [interp a] gives the interpretation of abbreviation [a]. *)
val interp : data -> Notation_term.interpretation

(** [full_path a] gives the full path of abbreviation [a]. *)
val full_path : data -> Libnames.full_path

(** [enabled a] indicates whether the abbreviation [a] is enabled. *)
val enabled : data -> bool

(** [only_parsing a] indicates whether the abbreviation [a] is only used for
    parsing, and not for printing. *)
val only_parsing : data -> bool

(** [fold f acc] folds function [f] over the current abbreviation map, using
    [acc] as the initial accumulator value. *)
val fold : (Globnames.abbreviation -> data -> 'a -> 'a) -> 'a -> 'a

(** [find_opt k] gives the abbreviation associated with the key [k] in the
    abbreviation map, if there is one. *)
val find_opt : Globnames.abbreviation -> data option

(** [find_interp k] gives the interpretation of the abbreviation associated
    with the key [k] in the abbreviation map. The [Not_found] exception is
    raised if [k] is not mapped. *)
val find_interp : Globnames.abbreviation -> Notation_term.interpretation

(** [toggle ~on ~use key] actives (if [on]) or deactivates (if [not on]) the
    abbreviation with the given [key]. An abbreviation associated with [key]
    should exist, otherwise [Not_found] is raised. *)
val toggle : on:bool -> use:notation_use -> Globnames.abbreviation -> unit

(** [toggle_if ~on ~use pred] is equivalent to running [toggle ~on ~use] on
    all abbreviations satisfying the given predicate [pred]. *)
val toggle_if : on:bool -> use:notation_use ->
  (Globnames.abbreviation -> data -> bool) -> unit

val declare : Summary.Interp.mut ->
  local:Libobject.locality ->
  Globnames.extended_global_reference UserWarn.with_qf option ->
  Id.t ->
  onlyparsing:bool -> Notation_term.interpretation -> unit

val import : int -> Libnames.full_path -> Globnames.abbreviation -> Summary.Interp.mut -> unit
