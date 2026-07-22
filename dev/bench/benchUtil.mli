(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type char_loc = {
  start_char : int;
  stop_char : int;
}

type source_loc = {
  chars : char_loc;
  line : int;
  text : string;
}

(** A measurement, with the original printed string and an exact rational representation *)
type measure = { str: string; q: Q.t; }

val dummy_measure : measure

type memory = {
  major_words : string;
  minor_words : string;
  major_collect : int;
  minor_collect : int;
  heap_words : int option;
}

type gc_collections = {
  major : int;
  minor : int;
}
(** Collections observed between two adjacent profiled commands. *)

type data = {
  time : measure;
  memory : memory option;
  instructions : int option;
  gc_before : gc_collections option;
  (** Collections between the preceding command and this command. [None] means
      there is no preceding command or the profile has no boundary data. *)
  gc_after : gc_collections option;
  (** Collections between this command and the following command. [None] means
      there is no following command or the profile has no boundary data. *)
}

val dummy_data : data

val combine_related_data : (string * (char_loc * 'a) array) array -> (char_loc * 'a array) array
(** Combine data from multiple files about the same source, ensuring
    that the locations do not have inconsistencies. *)

val read_whole_file : string -> string
