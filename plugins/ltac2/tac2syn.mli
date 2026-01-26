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
open Tac2expr

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

type notation_data =
  | UntypedNota of raw_tacexpr
  | TypedNota of {
      nota_prms : int;
      nota_argtys : int glb_typexpr Id.Map.t;
      nota_ty : int glb_typexpr;
      nota_body : glb_tacexpr;
    }

val interp_notation : ?loc:Loc.t -> tacsyn -> notation_data * (lname * raw_tacexpr) list

type 'body notation_interpretation

val ltac2_notation_cat : Libobject.category

type notation_target = Libnames.qualid option * int option

val pr_register_notation : sexpr list -> notation_target -> raw_tacexpr -> Pp.t

val register_notation : Attributes.vernac_flags -> sexpr list ->
  notation_target -> 'body -> 'body notation_interpretation
(** Does not handle the deprecated abbreviation syntax *)

val intern_notation_interpretation : (Id.Set.t -> 'raw -> 'glb) -> 'raw notation_interpretation ->
  'glb notation_interpretation

val register_notation_interpretation : notation_data notation_interpretation -> unit

val register_custom_entry : lident -> unit

module Internal : sig
  (** Re-exported in Tac2entries.Pltac *)
  val ltac2_expr : raw_tacexpr Procq.Entry.t
end
