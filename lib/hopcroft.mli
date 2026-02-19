(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Hopcroft algorithm *)

module type S =
sig
  type label
  type state
  type transition = {
    src : state;
    lbl : label;
    dst : state;
  }

  type automaton = {
    states : int;
    (** The number of states of the automaton. *)
    partitions : state list list;
    (** A set of state partitions initially known to be observationally
        distinct. For instance, if the automaton has the list [l] as accepting
        states, one can set [partitions = [l]]. *)
    transitions : transition list;
    (** The transitions of the automaton without duplicates. *)
  }

  val reduce : automaton -> state list array
  (** Associate the array of equivalence classes of the states of an automaton *)
end

module Make (Label : Map.OrderedType) : S with type label = Label.t and type state = int
