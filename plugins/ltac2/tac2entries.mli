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

val register_ltac : ?deprecation:Deprecation.t -> ?local:bool -> ?mut:bool -> rec_flag ->
  (Names.lname * raw_tacexpr) list -> unit

val register_type : ?local:bool -> ?abstract:bool -> rec_flag ->
  (qualid * redef_flag * raw_quant_typedef) list -> unit

val import_type : qualid -> Id.t -> unit

val register_primitive : ?deprecation:Deprecation.t -> ?local:bool ->
  Names.lident -> raw_typexpr -> ml_tactic_name -> unit

val register_struct : Attributes.vernac_flags -> strexpr -> unit

type _ notation_interpretation_data

type notation_target = qualid option * int option

val pr_register_notation : sexpr list -> notation_target -> raw_tacexpr -> Pp.t

val pr_register_abbreviation : Id.t CAst.t -> raw_tacexpr -> Pp.t

val register_notation : Attributes.vernac_flags -> sexpr list ->
  notation_target -> 'body -> 'body notation_interpretation_data

val register_abbreviation : Attributes.vernac_flags -> Id.t CAst.t ->
  'body -> 'body notation_interpretation_data

val register_notation_interpretation : raw_tacexpr notation_interpretation_data -> unit

val register_custom_entry : lident -> unit

val perform_eval : pstate:Declare.Proof.t option -> raw_tacexpr -> unit

(** {5 Notations} *)

module Tac2Custom : module type of KerName

module CustomTab : Nametab.NAMETAB with type elt = Tac2Custom.t

val find_custom_entry : Tac2Custom.t -> raw_tacexpr Procq.Entry.t
(** NB: Do not save the result of this function across summary resets,
    the Entry.t gets regenerated on (parsing) summary unfreeze. *)

module Syntax : sig

  (** Type of notation syntax parsing ['a].
      Unlike [Procq.Symbol.t] it fully supports comparison and is marshallable. *)
  type 'a t

  (** Sequence of [t]. *)
  type 'a seq

  (** Marshal-stable proxy for [Procq.Entry.t]. *)
  type 'a entry

  (** Must be called at toplevel, with non backtrackable entry.
      [name] defaults to the entry name but can be given another value if there is a conflict.
      Registering the same entry twice produces different [entry] values. *)
  val register_entry : ?name:string -> 'a Procq.Entry.t -> 'a entry

  (** Pre-registered entries. *)

  val constr : Constrexpr.constr_expr entry
  val lconstr : Constrexpr.constr_expr entry
  val term : Constrexpr.constr_expr entry
  val custom_constr : Globnames.CustomName.t -> Constrexpr.constr_expr entry

  (* XXX make pltac use Syntax.entry? currently its entries are
     registered in tac2extravals (but maybe not all of them) *)
  val ltac2_expr : raw_tacexpr entry
  val custom_ltac2 : Tac2Custom.t -> raw_tacexpr entry

  (** Constructors for [t], copying [Procq.Symbol] constructors. *)

  val nterm : 'a entry -> 'a t
  val nterml : 'a entry -> string -> 'a t
  val list0 : ?sep:string -> 'a t -> 'a list t
  val list1 : ?sep:string -> 'a t -> 'a list t
  val opt : 'a t -> 'a option t
  val self : raw_tacexpr t
  val next : raw_tacexpr t
  val token : 'a Tok.p -> 'a t
  val tokens : Procq.ty_pattern list -> unit t

  (** Instead of [rules] we have the less general [seq]. *)
  val seq : 'a seq -> 'a t

  val nil : unit seq
  val snoc : 'a seq -> 'b t -> ('a * 'b) seq
end

type syntax_class_rule =
| SyntaxRule : 'a Syntax.t * ('a -> raw_tacexpr) -> syntax_class_rule

type used_levels

val no_used_levels : used_levels

val union_used_levels : used_levels -> used_levels -> used_levels

type 'glb syntax_class_decl = {
  intern_synclass : sexpr list -> used_levels * 'glb;
  interp_synclass : 'glb -> syntax_class_rule;
}

val register_syntax_class : Id.t -> _ syntax_class_decl -> unit
(** Create a new syntax class with the provided name *)

type syntax_class

val intern_syntax_class : sexpr -> used_levels * syntax_class
(** Use this to internalize the syntax class arguments for interpretation functions *)

val interp_syntax_class : syntax_class -> syntax_class_rule
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

(** {5 Eval loop} *)

(** Evaluate a tactic expression in the current environment *)
val call : pstate:Declare.Proof.t -> Goal_select.t option -> with_end_tac:bool CAst.t -> raw_tacexpr
  -> Declare.Proof.t

val call_par : pstate:Declare.Proof.t -> raw_tacexpr -> Declare.Proof.t

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
