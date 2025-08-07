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
open Tactypes
open HypNaming
open Logic

(** Basic introduction tactics. See [introPattern.ml] for variants which deal
    with introduction patterns (i.e. which allow destructing introduced variables). *)


val is_quantified_hypothesis : Id.t -> Proofview.Goal.t -> bool

(** {6 Introducing a single variable. } *)

(** [intro ?move ?force ?dep ?tac ?naming ()] introduces a single variable. The goal
    should be a product or a letin.
    - [move] is a move location for the introduced variable. Defaults to [MoveLast].
    - [force]: if [true], we are more aggressive. Specifically, if the goal is not
      a product or a letin we attempt to head-normalize it. Also if the goal
      is an evar we instantiate it with a product. Defaults to [false].
    - [dep]: if [true], we disallow introducing a variable which occurs
      in the body of the product/letin.
    - [tac]: tactic which is run once the variable has been introduced. It is given
      the name of the introduced variable. Defaults to [tclUNIT ()].
    - [naming] is used to name the hypothesis. Defaults to [NamingAvoid Id.Set.empty]. *)
val intro : ?move:(Id.t move_location) -> ?force:bool -> ?dep:bool ->
  ?tac:(Id.t -> unit Proofview.tactic) -> ?naming:name_flag -> unit -> unit Proofview.tactic

(** Specialization of [intro] to [NamingMustBe id]. *)
val intro_mustbe : ?move:(Id.t move_location) -> ?force:bool -> ?dep:bool ->
  ?tac:(Id.t -> unit Proofview.tactic) -> Id.t -> unit Proofview.tactic

(** Specialization of [intro] to [NamingBasedOn (id, Id.Set.empty)]. *)
val intro_basedon : ?move:(Id.t move_location) -> ?force:bool -> ?dep:bool ->
  ?tac:(Id.t -> unit Proofview.tactic) -> Id.t -> unit Proofview.tactic

(** [intro_replacing id] introduces a single variable named [id], replacing the previous declaration of [id].
    Fails if [id] is not already in the context. *)
val intro_replacing : Id.t -> unit Proofview.tactic

(** {6 Introducing multiple variables. }*)

(** [intros] keeps introducing variables while the goal is a product or a let-in. *)
val intros : unit Proofview.tactic

(** [intros_until hyp] is a variant of [intros] which stops when hypothesis [hyp] is introduced. *)
val intros_until : quantified_hypothesis -> unit Proofview.tactic

(** Generalization of [intro] to a list of variables and locations (processed from left to right). *)
val intros_move : (Id.t * Id.t Logic.move_location) list -> unit Proofview.tactic

(** Generalization of [intro_mustbe] to a list of variables (processed from left to right). *)
val intros_mustbe : ?force:bool -> Id.t list -> unit Proofview.tactic

(** Generalization of [intro_basedon] to a list of variables (processed from left to right). *)
val intros_basedon : ?force:bool -> ?tac:(Id.t list -> unit Proofview.tactic) -> Id.t list -> unit Proofview.tactic

(** Generalization of [intro_replacing] to a list of variables (processed from left to right). *)
val intros_replacing : Id.t list -> unit Proofview.tactic

(** Variant of [intros_replacing] which does not assume that the variables are
    already declared in the context. *)
val intros_possibly_replacing : Id.t list -> unit Proofview.tactic

(** Low-level variant of [intros]. Use with caution. *)
val intro_forthcoming : Id.Set.t -> ?move:(Id.t move_location) -> ?dep:bool -> ?bound:(int option) ->
    ?start:int -> ?tac:(Id.t list -> unit Proofview.tactic) -> unit -> unit Proofview.tactic

(** [auto_intros_tac names] introduces the variables in [names].
    - The variables are introduced from right to left (contrary to the conventional order).
    - Names are chosen as follow: [Anonymous] indicates to generate a fresh name
      and [Name id] indicates to use the name [id].
    - It will instantiate evars and head-normalize the goal in the same way as [introf]. *)
val auto_intros_tac : Names.Name.t list -> unit Proofview.tactic

val try_intros_until_id_check : Id.t -> unit Proofview.tactic

(** [intros_clearing bs] introduces as many variables as booleans in [bs]. Each boolean indicates
    whether to clear the introduced variable (if [true]) or to keep it (if [false]). *)
val intros_clearing : bool list -> unit Proofview.tactic

(** Assuming a tactic [tac] depending on a hypothesis,
    [try_intros_until tac arg] first assumes that [arg] denotes a
    quantified hypothesis (denoted by name or by index) and tries to
    introduce it in context before applying [tac], otherwise assumes the
    hypothesis is already in context and directly applies [tac]. *)
val try_intros_until :
  (Id.t -> unit Proofview.tactic) -> quantified_hypothesis -> unit Proofview.tactic
