(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Evd

(** Proofs, these functions obey [Hyps Limit] and [Compact contexts]. *)

(** [pr_open_subgoals ~quiet ?oldp proof] shows the context for [proof] as used by, for example, coqtop.
    The first active goal is printed with all its antecedents and the conclusion.  The other active goals only show their
     conclusions.  If [oldp] is [Some oproof], highlight the differences between the old proof [oproof], and [proof].  [quiet]
     disables printing messages as Feedback.
*)
val pr_open_subgoals : ?quiet:bool -> ?oldp:Proof.t option option -> ?flags:PrintingFlags.t ->
  Proof.t -> Pp.t
val pr_nth_open_subgoal : ?flags:PrintingFlags.t ->
  ?oldp:Proof.t option option -> proof:Proof.t -> int -> Pp.t

val pr_goal_by_id : ?flags:PrintingFlags.t ->
  ?oldp:Proof.t option option -> proof:Proof.t -> Libnames.qualid -> Pp.t
val pr_goal_emacs : ?flags:PrintingFlags.t ->
  proof:Proof.t option -> int -> int -> Pp.t

(** Tells if goal name should be printed, i.e., either "Printing Goal Names" flag is activated,
    or the evar was given a name. *)
val print_goal_name : evar_map -> Evar.t -> bool
