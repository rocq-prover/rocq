(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This files implements auto and related automation tactics *)

open Names
open EConstr
open Pattern
open Hints
open Tactypes

val compute_secvars : Proofview.Goal.t -> Id.Pred.t

(** Default maximum search depth used by [auto] and [trivial]. *)
val default_search_depth : int

val auto_flags_of_state : TransparentState.t -> Unification.unify_flags

(** Try unification with the precompiled clause, then use registered Apply *)
val unify_resolve : Unification.unify_flags -> hint -> unit Proofview.tactic

(** [ConclPattern concl pat tacast]:
   if the term concl matches the pattern pat, (in sense of
   [Pattern.somatches], then replace [?1] [?2] metavars in tacast by the
   right values to build a tactic *)
val conclPattern : constr -> constr_pattern option -> Gentactic.glob_generic_tactic -> unit Proofview.tactic

(** [default_auto] runs the tactic [auto] with:
    - Maximum search depth [default_search_depth].
    - The hint database ["core"].
    - No additional lemma. *)
val default_auto : unit Proofview.tactic

(** [gen_auto ?debug depth lemmas hints] runs the tactic [auto].
    - [debug] controls whether to print a debug trace ([Off] by default). [Off] prints nothing,
      [Info] prints successful steps, and [Debug] prints all steps (including unsuccessful ones).
    - [depth] is the maximum search depth. If [None], [default_search_depth] is used.
    - [lemmas] contains additional lemmas for [auto] to use.
    - [hints] is a list of hint databases to use. If [None], _all_ existing hint databases are used.
      By default the ["core"] hint database is included: passing ["nocore"]
      will disable ["core"]. *)
val gen_auto : ?debug:debug ->
  int option -> delayed_open_constr list -> hint_db_name list option -> unit Proofview.tactic

(** [gen_trivial] runs the tactic [trivial].
    See [gen_auto] for an explanation of the different options.*)
val gen_trivial : ?debug:debug ->
  delayed_open_constr list -> hint_db_name list option -> unit Proofview.tactic
