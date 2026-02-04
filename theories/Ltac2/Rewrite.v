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
From Ltac2 Require Std.

(** Module for rewrite strategies used by [rewrite_strat]. *)
Module Strategy.
  Ltac2 Type t.

  (** Failure. *)
  Ltac2 @external fail : t :=
    "rocq-runtime.plugins.ltac2" "rewstrat_fail".

  (** Success without progress. *)
  Ltac2 @external id : t :=
    "rocq-runtime.plugins.ltac2" "rewstrat_id".

  (** Success with progress. *)
  Ltac2 @external refl : t :=
    "rocq-runtime.plugins.ltac2" "rewstrat_refl".

  (** Applies the argument and fails if no progress was made. *)
  Ltac2 @external progress : t -> t :=
    "rocq-runtime.plugins.ltac2" "rewstrat_progress".

  (** Applies left, and then right if left succeeded.  *)
  Ltac2 @external seq : t -> t -> t :=
    "rocq-runtime.plugins.ltac2" "rewstrat_seq".

  (** Equivalent to [List.fold_left seq id]. *)
  Ltac2 @external seqs : t list -> t :=
    "rocq-runtime.plugins.ltac2" "rewstrat_seqs".

  (** Applies left, and then right if left failed. *)
  Ltac2 @external choice : t -> t -> t :=
    "rocq-runtime.plugins.ltac2" "rewstrat_choice".

  (** Equivalent to [List.fold_left choice fail]. *)
  Ltac2 @external choices : t list -> t :=
    "rocq-runtime.plugins.ltac2" "rewstrat_choices".

  (** Equivalent to [choice s id]. *)
  Ltac2 @external try : t -> t :=
    "rocq-runtime.plugins.ltac2" "rewstrat_try".

  (** Applies the argument until it fails. *)
  Ltac2 @external any : t -> t :=
    "rocq-runtime.plugins.ltac2" "rewstrat_any".

  (** Equivalent to [seq s (any s)]. *)
  Ltac2 @external repeat : t -> t :=
    "rocq-runtime.plugins.ltac2" "rewstrat_repeat".

  (** Applies the argument to all immediate subterms of the considered term,
      left-to-right. *)
  Ltac2 @external subterms : t -> t :=
    "rocq-runtime.plugins.ltac2" "rewstrat_all_subterms".

  (** Applies the argument to the leftmost immediate subterm of the considered
      term on which progress can be made. *)
  Ltac2 @external subterm : t -> t :=
    "rocq-runtime.plugins.ltac2" "rewstrat_one_subterm".

  (** Traverses the term bottom-up--left-to-right and applies the argument at
      each step as many times as possible. *)
  Ltac2 @external bottomup : t -> t :=
    "rocq-runtime.plugins.ltac2" "rewstrat_bottomup".

  (** Traverses the term top-down--left-to-right and applies the argument at
      each step as many times as possible. *)
  Ltac2 @external topdown : t -> t :=
    "rocq-runtime.plugins.ltac2" "rewstrat_topdown".

  (** Traverses the term bottom-up--left-to-right until the argument makes progress. *)
  Ltac2 @external innermost : t -> t :=
    "rocq-runtime.plugins.ltac2" "rewstrat_innermost".

  (** Traverses the term top-down--left-to-right until the argument makes progress. *)
  Ltac2 @external outermost : t -> t :=
    "rocq-runtime.plugins.ltac2" "rewstrat_outermost".

  (** Unifies the one side of the lemma with the current subterm and on success
      rewrite it to the other side. If the boolean argument is true, rewrites
      left-to-right; otherwise, rewrites right-to-left. *)
  Ltac2 @external term : preterm -> bool -> t :=
    "rocq-runtime.plugins.ltac2" "rewstrat_one_lemma".

  (** Equivalent to [choices (List.map (fun c => term c true)) l]. *)
  Ltac2 @external terms : preterm list -> t :=
    "rocq-runtime.plugins.ltac2" "rewstrat_lemmas".

  (* TODO this needs documentation *)
  Ltac2 @external old_hints : ident -> t :=
    "rocq-runtime.plugins.ltac2" "rewstrat_old_hints".

  (** Applies hints from rewrite hint database. *)
  Ltac2 @external hints : ident -> t :=
    "rocq-runtime.plugins.ltac2" "rewstrat_hints".

  (** Replaces the term under consideration with the argument if they unify. *)
  Ltac2 @external fold : constr -> t :=
    "rocq-runtime.plugins.ltac2" "rewstrat_fold".

  (** Converts the term under consideration. *)
  Ltac2 @external eval : Std.Red.t -> t :=
    "rocq-runtime.plugins.ltac2" "rewstrat_eval".

  (** Fixed point operation for recursive strategies. [fix (fun f => s)] evaluates
      to [s[f / fix (fun f => s)]]. The function provided in the argument is
      executed only _once_ when the strategy is constructed — it cannot be used
      for dynamically manage the rewriting. *)
  Ltac2 @external fix_ : (t -> t) -> t :=
    "rocq-runtime.plugins.ltac2" "rewstrat_fix".

  (** The identity if the pattern matching succeeds, fails otherwise *)
  Ltac2 @external matches : pattern -> t :=
    "rocq-runtime.plugins.ltac2" "rewstrat_matches".

  (** The rewrite success datatype, where [prf] should be of type [rel lhs rhs] *)
  Ltac2 Type rewrite_success := { rel : constr; rhs : constr; prf : constr }.

  (** A rewrite result can be any of a success, and identity step (no progress), or a failure *)
  Ltac2 Type rewrite_result := [ Success (rewrite_success) | Identity | Fail ].

  (** The [tactic f] strategy applies [f] to arguments [ty], [lhs] and [rel],
      where [lhs] is the subterm being rewritten, of type [ty], and
      an optional relation constraint [rel] is given.

      The tactic is applied to a single goal of type [unit] whose context
      corresponds to the context of the term to rewrite (i.e. the context of the
      goal at the start of the [rewrite_strat] call extended with the binders
      that were traversed to attain this subterm. The tactic should return a
      [rewrite_result] indicating success, failure or no progress and should
      *not* solve the goal. Solving the goal is an error that aborts the
      [rewrite_strat] call. The success record contains the chosen relation
      [rel], new right hand-side [rhs] and a proof [prf] of [rel t rhs].

      If the proof [prf] is syntactically [eq_refl _], then the witness
      of the rewriting is simply a *conversion* requiring no explicit
      proof and no congruence lemmas for the context of the rewrite.
   *)
  Ltac2 @external tactic : (constr -> constr -> constr option -> rewrite_result) -> t :=
    "rocq-runtime.plugins.ltac2" "rewstrat_tactic".

End Strategy.

(* Tactics *)

(** Runs rewrite strategy on the type of a hypothesis or the goal if the second
    argument is [None]. *)
Ltac2 @external rewrite_strat : Strategy.t -> ident option -> unit := "rocq-runtime.plugins.ltac2" "tac_rewrite_strat".

(** Runs rewritings from a hint database on the type of a hypothesis or the goal
    if the second argument is [None]. The rewritings are applied top-down on all
    subterms. *)
Ltac2 rewrite_db (hintdb : ident) (i : ident option) : unit := rewrite_strat (Strategy.topdown (Strategy.hints hintdb)) i.
