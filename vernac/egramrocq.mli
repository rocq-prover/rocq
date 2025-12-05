(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Mapping of grammar productions to camlp5 actions *)

(** This is the part specific to Rocq-level Notation and Tactic Notation.
    For the ML-level tactic and vernac extensions, see Egramml. *)

(** {5 Adding notations} *)

val extend_constr_grammar : Summary.Synterp.mut -> Notation_gram.one_notation_grammar -> unit
(** Add a term notation rule to the parsing system. *)

val find_custom_entry_g : Procq.GramState.t -> Globnames.CustomName.t ->
  Constrexpr.constr_expr Procq.Entry.t * Constrexpr.cases_pattern_expr Procq.Entry.t

val find_custom_entry : Summary.Synterp.t -> Globnames.CustomName.t ->
  Constrexpr.constr_expr Procq.Entry.t * Constrexpr.cases_pattern_expr Procq.Entry.t

val create_custom_entry : Summary.Synterp.mut -> Globnames.CustomName.t -> unit
(** Add the entry to the grammar. *)
