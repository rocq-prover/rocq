(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open BenchUtil

val join_to_source : dummy:'a -> source:string -> (char_loc * 'a) list -> (source_loc * 'a) list
(** Given a list of values ordered by locations with no overlaps but
    maybe gaps, associate them to substrings of the source and fill in
    the gaps using [dummy].

    When a gap ends with whitespace (not newlines) that whitespace is merged into the next value.

    An all-blank gap at the end is dropped.
*)
