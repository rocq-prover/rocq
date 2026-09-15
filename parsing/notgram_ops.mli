(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Merge with metasyntax? *)
open Constrexpr
open Notation_gram

(** {6 Declare the parsing rules and entries of a (possibly uninterpreted) notation } *)

val declare_notation_grammar : notation -> notation_grammar -> unit
val grammar_of_notation : notation -> notation_grammar
  (** raise [Not_found] if not declared *)

val declare_notation_non_terminals : notation -> Extend.constr_entry_key list -> unit
val non_terminals_of_notation : notation -> Extend.constr_entry_key list

(** [declare_notation_prefixes ntn] makes [ntn] eligible as an answer of
    [longest_common_prefix].  Later notations sharing a prefix with [ntn] take
    their default levels from it, and are checked against it for
    factorization.  So call this only for a notation that has a parsing rule of
    its own.  An "only printing" notation has none, and registering one leaks
    its levels into the grammar of those later notations. *)
val declare_notation_prefixes : notation -> unit

(** [longest_common_prefix ntn] looks among notations [ntn'] already
    registered with [declare_notation_prefixes ntn'] for the one
    that shares the longest common prefix with [ntn], if any returns
    [Some (ntn', k)] where [k] is the number of nonterminal symbols in
    the common prefix between [ntn] and [ntn']. *)
val longest_common_prefix : notation -> (notation * int) option

(** Returns notations with defined parsing/printing rules *)
val get_defined_notations : unit -> notation list
