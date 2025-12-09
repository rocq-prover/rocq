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
open Libnames
open Tac2expr

(** {5 Toplevel definitions} *)

val register_ltac : Summary.Interp.mut ->
  ?deprecation:Deprecation.t -> ?local:bool -> ?mut:bool -> rec_flag ->
  (Names.lname * raw_tacexpr) list -> unit

val register_type : Summary.Interp.mut ->
  ?local:bool -> ?abstract:bool -> rec_flag ->
  (qualid * redef_flag * raw_quant_typedef) list -> unit

val import_type : Summary.Interp.mut ->
  qualid -> Id.t -> unit

val register_primitive : Summary.Interp.mut ->
  ?deprecation:Deprecation.t -> ?local:bool ->
  Names.lident -> raw_typexpr -> ml_tactic_name -> unit

val register_struct : Summary.Interp.mut ->
  Attributes.vernac_flags -> strexpr -> unit

type notation_interpretation_data

type notation_target = qualid option * int option

val pr_register_notation : sexpr list -> notation_target -> raw_tacexpr -> Pp.t

val pr_register_abbreviation : Id.t CAst.t -> raw_tacexpr -> Pp.t

val register_notation : Summary.Synterp.mut ->
  Attributes.vernac_flags -> sexpr list ->
  notation_target -> raw_tacexpr -> notation_interpretation_data

val register_abbreviation : Attributes.vernac_flags -> Id.t CAst.t ->
  raw_tacexpr -> notation_interpretation_data

val register_notation_interpretation : Summary.Interp.mut ->
  notation_interpretation_data -> unit

val register_custom_entry : Summary.Synterp.mut -> lident -> unit

val perform_eval : pstate:Declare.Proof.t option -> raw_tacexpr -> unit

(** {5 Notations} *)

type syntax_class_rule =
| SyntaxRule : (raw_tacexpr, _, 'a) Procq.Symbol.t * ('a -> raw_tacexpr) -> syntax_class_rule

type used_levels

val no_used_levels : used_levels

val union_used_levels : used_levels -> used_levels -> used_levels

type 'glb syntax_class_decl = {
  intern_synclass : sexpr list -> used_levels * 'glb;
  interp_synclass : Procq.FullState.t -> 'glb -> syntax_class_rule;
}

val register_syntax_class : Id.t -> _ syntax_class_decl -> unit
(** Create a new syntax class with the provided name *)

type syntax_class

val intern_syntax_class : sexpr -> used_levels * syntax_class
(** Use this to internalize the syntax class arguments for interpretation functions *)

val interp_syntax_class : Procq.FullState.t -> syntax_class -> syntax_class_rule
(** Use this to interpret the syntax class arguments for interpretation functions *)

(** {5 Inspecting} *)

val print_located_tactic : Libnames.qualid -> unit
(** Display the absolute name of a tactic. *)

val print_ltac2 : Libnames.qualid -> unit
(** Display the definition of a tactic. *)

val print_ltac2_type : Libnames.qualid -> unit
(** Display the definition of a type. *)

val print_signatures : unit -> unit
(** Print types of all definitions in scope. *)

val typecheck_expr : raw_tacexpr -> unit

val globalize_expr : raw_tacexpr -> unit

module Tac2Custom : module type of KerName

module CustomTab : Nametab.NAMETAB with type elt = Tac2Custom.t

val find_custom_entry_g : Procq.GramState.t -> Tac2Custom.t -> raw_tacexpr Procq.Entry.t
val find_custom_entry : Summary.Synterp.t -> Tac2Custom.t -> raw_tacexpr Procq.Entry.t
(** NB: Do not save the result of this function across summary resets,
    the Entry.t gets regenerated on (parsing) summary unfreeze. *)

(** {5 Eval loop} *)

(** Evaluate a tactic expression in the current environment *)
val call : pstate:Declare.Proof.t -> Goal_select.t option -> with_end_tac:bool CAst.t -> raw_tacexpr
  -> Declare.Proof.t

val call_par : Summary.Interp.t ->
  pstate:Declare.Proof.t -> raw_tacexpr -> Declare.Proof.t

(** {5 Parsing entries} *)

module Pltac :
sig
val ltac2_expr : raw_tacexpr Procq.Entry.t
val tac2expr_in_env : (Id.t CAst.t list * raw_tacexpr) Procq.Entry.t

(** Quoted entries. To be used for complex notations. *)

open Tac2qexpr

val q_ident : Id.t CAst.t or_anti Procq.Entry.t
val q_bindings : bindings Procq.Entry.t
val q_with_bindings : bindings Procq.Entry.t
val q_intropattern : intro_pattern Procq.Entry.t
val q_intropatterns : intro_pattern list CAst.t Procq.Entry.t
val q_destruction_arg : destruction_arg Procq.Entry.t
val q_induction_clause : induction_clause Procq.Entry.t
val q_conversion : conversion Procq.Entry.t
val q_orient : orientation Procq.Entry.t
val q_rewriting : rewriting Procq.Entry.t
val q_clause : clause Procq.Entry.t
val q_dispatch : dispatch Procq.Entry.t
val q_occurrences : occurrences Procq.Entry.t
val q_reference : reference or_anti Procq.Entry.t
val q_strategy_flag : strategy_flag Procq.Entry.t
val q_constr_matching : constr_matching Procq.Entry.t
val q_goal_matching : goal_matching Procq.Entry.t
val q_hintdb : hintdb Procq.Entry.t
val q_move_location : move_location Procq.Entry.t
val q_pose : pose Procq.Entry.t
val q_assert : assertion Procq.Entry.t
end
