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
open Vernacexpr
open Notation
open Constrexpr
open Notation_term
open Environ

type notation_main_data
type syntax_rules

type notation_interpretation_decl
(** This data type packages all the necessary information to declare a notation
    interpretation, once the syntax is declared or recovered from a previous
    declaration. *)

val add_notation_syntax :
  Summary.Synterp.mut ->
  local:bool ->
  infix:bool ->
  UserWarn.t option ->
  notation_declaration ->
  notation_interpretation_decl
(** Add syntax rules for a (constr) notation in the environment *)

val add_notation_interpretation :
  Summary.Interp.mut ->
  local:bool -> env -> notation_interpretation_decl -> unit
(** Declare the interpretation of a notation *)

(** Declaring scopes, delimiter keys and default scopes *)

val declare_scope : Summary.Interp.mut -> locality_flag -> scope_name -> unit
val add_delimiters : Summary.Interp.mut -> locality_flag -> scope_name -> string -> unit
val remove_delimiters : Summary.Interp.mut -> locality_flag -> scope_name -> unit
val add_class_scope : Summary.Interp.mut -> locality_flag -> scope_name -> add_scope_where option -> scope_class list -> unit

(** Scope opening *)

val open_close_scope : Summary.Interp.mut -> locality_flag -> to_open:bool -> scope_name -> unit

(** Add a notation interpretation associated to a "where" clause (already has pa/pp rules) *)

val prepare_where_notation :
  notation_declaration -> notation_interpretation_decl
  (** Interpret the modifiers of a where-notation *)

val set_notation_for_interpretation :
  Summary.Interp.mut -> env -> Constrintern.internalization_env -> notation_interpretation_decl -> unit
(** Set the interpretation of the where-notation for interpreting a mutual block.
    Does not add persistent state (libobject). *)

(** Add only the parsing/printing rule of a notation *)

val add_reserved_notation :
  Summary.Synterp.mut -> local:bool -> infix:bool -> (lstring * syntax_modifier CAst.t list) -> unit

(** Add a syntactic definition (as in "Notation f := ...") *)

val add_abbreviation : Summary.Interp.mut ->
  local:Libobject.locality -> Globnames.extended_global_reference UserWarn.with_qf option -> env ->
  Id.t -> Id.t list * constr_expr -> syntax_modifier CAst.t list -> unit

(** Print the Camlp5 state of a grammar *)

val pr_grammar : Summary.Synterp.t -> string list -> Pp.t
val pr_custom_grammar : Summary.Synterp.t -> Libnames.qualid -> Pp.t
val pr_keywords : Summary.Synterp.t -> Pp.t

(** Register a handler for Print Custom Grammar. The handler should
    return [None] for unknown entries and [Some] of the associated
    entries for known entries. *)
val register_custom_grammar_for_print :
  (Summary.Synterp.t -> Libnames.qualid -> Procq.Entry.any_t list option) -> unit

(* XXX also handles interp phase summaries *)
val with_syntax_protection : (Summary.Synterp.mut -> 'a) -> Summary.Synterp.t -> 'a

val declare_notation_toggle : Summary.Interp.mut ->
  locality_flag -> on:bool -> all:bool -> Notation.notation_query_pattern -> unit

val declare_custom_entry : Summary.Synterp.mut -> locality_flag -> Id.t -> unit
(** Declare given string as a custom grammar entry *)

val intern_custom_name : Libnames.qualid -> Globnames.CustomName.t
(** Intern custom entry name using compat layer if needed. *)

val intern_notation_entry : Libnames.qualid notation_entry_gen -> notation_entry
(** Intern notation entry name using compat layer for custom entries if needed. *)

val pr_level : notation_entry_level * entry_relative_level list -> Extend.constr_entry_key list -> Pp.t
(** Pretty print level information of a notation and all of its arguments *)
