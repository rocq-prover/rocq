(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Ltac2 Require Import Init.

Ltac2 Type strategy.


(** Failure. *)
Ltac2 @external fail : strategy :=
  "rocq-runtime.plugins.ltac2" "rewstrat_fail".

(** Success without progress. *)
Ltac2 @external id : strategy :=
  "rocq-runtime.plugins.ltac2" "rewstrat_id".

(** Success with progress. *)
Ltac2 @external refl : strategy :=
  "rocq-runtime.plugins.ltac2" "rewstrat_refl".

(** Applies the argument and fails if no progress was made. *)
Ltac2 @external progress : strategy -> strategy :=
  "rocq-runtime.plugins.ltac2" "rewstrat_progress".

(** Applies left, and then right if left succeeded.  *)
Ltac2 @external seq : strategy -> strategy -> strategy :=
  "rocq-runtime.plugins.ltac2" "rewstrat_seq".

(** Equivalent to [List.fold_left seq id]. *)
Ltac2 @external seqs : strategy list -> strategy :=
  "rocq-runtime.plugins.ltac2" "rewstrat_seqs".

(** Applies left, and then right if left failed. *)
Ltac2 @external choice : strategy -> strategy -> strategy :=
  "rocq-runtime.plugins.ltac2" "rewstrat_choice".

(** Equivalent to [List.fold_left choice fail]. *)
Ltac2 @external choices : strategy list -> strategy :=
  "rocq-runtime.plugins.ltac2" "rewstrat_choices".

(** Equivalent to [choice s id]. *)
Ltac2 @external try : strategy -> strategy :=
  "rocq-runtime.plugins.ltac2" "rewstrat_try".

(** Applies the argument until it fails. *)
Ltac2 @external any : strategy -> strategy :=
  "rocq-runtime.plugins.ltac2" "rewstrat_any".

(** Equivalent to [seq s (any s)]. *)
Ltac2 @external repeat : strategy -> strategy :=
  "rocq-runtime.plugins.ltac2" "rewstrat_repeat".

(** Applies the argument to all immediate subterms of the considered term,
left-to-right. *)
Ltac2 @external subterms : strategy -> strategy :=
  "rocq-runtime.plugins.ltac2" "rewstrat_all_subterms".

(** Applies the argument to the leftmost immediate subterm of the considered
term on which progress can be made. *)
Ltac2 @external subterm : strategy -> strategy :=
  "rocq-runtime.plugins.ltac2" "rewstrat_one_subterm".

(** Traverses the term bottom-up--left-to-right and applies the argument at each
step as many times as possible. *)
Ltac2 @external bottomup : strategy -> strategy :=
  "rocq-runtime.plugins.ltac2" "rewstrat_bottomup".

(** Traverses the term top-down--left-to-right and applies the argument at each
step as many times as possible. *)
Ltac2 @external topdown : strategy -> strategy :=
  "rocq-runtime.plugins.ltac2" "rewstrat_topdown".

(** Traverses the term bottom-up--left-to-right until the argument makes progress. *)
Ltac2 @external innermost : strategy -> strategy :=
  "rocq-runtime.plugins.ltac2" "rewstrat_innermost".

(** Traverses the term top-down--left-to-right until the argument makes progress. *)
Ltac2 @external outermost : strategy -> strategy :=
  "rocq-runtime.plugins.ltac2" "rewstrat_outermost".

(** Unifies the one side of the lemma with the current subterm and on success
rewrite it to the other side. If the boolean argument is true, rewrites
left-to-right; otherwise, rewrites right-to-left. *)
Ltac2 @external term : preterm -> bool -> strategy :=
  "rocq-runtime.plugins.ltac2" "rewstrat_one_lemma".

(** Equivalent to [choices (List.map (fun c => term c true)) l]. *)
Ltac2 @external terms : preterm list -> strategy :=
  "rocq-runtime.plugins.ltac2" "rewstrat_lemmas".

(* TODO this needs documentation *)
Ltac2 @external old_hints : ident -> strategy :=
  "rocq-runtime.plugins.ltac2" "rewstrat_old_hints".

(** Applies hints from rewrite hint database. *)
Ltac2 @external hints : ident -> strategy :=
  "rocq-runtime.plugins.ltac2" "rewstrat_hints".

(** Replaces the term under consideration with the argument if they unify. *)
Ltac2 @external fold : constr -> strategy :=
  "rocq-runtime.plugins.ltac2" "rewstrat_fold".

(** Fixed point operation for recursive strategies. [fix (fun f => s)] evaluates to
[s[f / fix (fun f => s)]]. The function provided in the argument is executed only
_once_ when the strategy is constructed — it cannot be used for dynamically
manage the rewriting. *)
Ltac2 @external fix_ : (strategy -> strategy) -> strategy :=
  "rocq-runtime.plugins.ltac2" "rewstrat_fix".

(* Tactics *)

Ltac2 @external rewrite_strat : strategy -> ident option -> unit := "rocq-runtime.plugins.ltac2" "tac_rewrite_strat".

Ltac2 rewrite_db (hintdb : ident) (i : ident option) : unit := rewrite_strat (topdown (hints hintdb)) i.
