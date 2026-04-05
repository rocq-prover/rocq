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
From Ltac2 Require Import Std.

Ltac2 Type kind.
(** An abstract type representing a scheme kind. Use the predefined values
    below to refer to specific scheme kinds. *)

Ltac2 @ external lookup : kind -> Std.reference -> Std.reference option
:= "rocq-runtime.plugins.ltac2" "scheme_lookup".
(** [Scheme.lookup kind ref] looks up the scheme registered under [kind] for
    the reference [ref]. Returns [None] if [ref] is not an inductive type or
    if no such scheme is registered. *)

(** {2 Elimination schemes} *)

Ltac2 @ external rect_dep : kind
:= "rocq-runtime.plugins.ltac2" "scheme_kind_rect_dep".
(** Dependent recursion scheme for Type. *)

Ltac2 @ external rec_dep : kind
:= "rocq-runtime.plugins.ltac2" "scheme_kind_rec_dep".
(** Dependent recursion scheme for Set. *)

Ltac2 @ external ind_dep : kind
:= "rocq-runtime.plugins.ltac2" "scheme_kind_ind_dep".
(** Dependent induction scheme for Prop. *)

Ltac2 @ external sind_dep : kind
:= "rocq-runtime.plugins.ltac2" "scheme_kind_sind_dep".
(** Dependent induction scheme for SProp. *)

Ltac2 @ external rect_nodep : kind
:= "rocq-runtime.plugins.ltac2" "scheme_kind_rect_nodep".
(** Non-dependent recursion scheme for Type. *)

Ltac2 @ external rec_nodep : kind
:= "rocq-runtime.plugins.ltac2" "scheme_kind_rec_nodep".
(** Non-dependent recursion scheme for Set. *)

Ltac2 @ external ind_nodep : kind
:= "rocq-runtime.plugins.ltac2" "scheme_kind_ind_nodep".
(** Non-dependent induction scheme for Prop. *)

Ltac2 @ external sind_nodep : kind
:= "rocq-runtime.plugins.ltac2" "scheme_kind_sind_nodep".
(** Non-dependent induction scheme for SProp. *)

(** {2 Case analysis schemes} *)

Ltac2 @ external case_dep : kind
:= "rocq-runtime.plugins.ltac2" "scheme_kind_case_dep".
(** Dependent case analysis scheme for Type. *)

Ltac2 @ external case_nodep : kind
:= "rocq-runtime.plugins.ltac2" "scheme_kind_case_nodep".
(** Non-dependent case analysis scheme for Type. *)

Ltac2 @ external casep_dep : kind
:= "rocq-runtime.plugins.ltac2" "scheme_kind_casep_dep".
(** Dependent case analysis scheme for Prop. *)

Ltac2 @ external casep_nodep : kind
:= "rocq-runtime.plugins.ltac2" "scheme_kind_casep_nodep".
(** Non-dependent case analysis scheme for Prop. *)

Ltac2 @ external scase_dep : kind
:= "rocq-runtime.plugins.ltac2" "scheme_kind_scase_dep".
(** Dependent case analysis scheme for SProp. *)

Ltac2 @ external scase_nodep : kind
:= "rocq-runtime.plugins.ltac2" "scheme_kind_scase_nodep".
(** Non-dependent case analysis scheme for SProp. *)

(** {2 Equality schemes} *)

Ltac2 @ external sym : kind
:= "rocq-runtime.plugins.ltac2" "scheme_kind_sym".
(** Symmetry scheme. *)

Ltac2 @ external sym_involutive : kind
:= "rocq-runtime.plugins.ltac2" "scheme_kind_sym_involutive".
(** Involutive symmetry scheme. *)

Ltac2 @ external rew : kind
:= "rocq-runtime.plugins.ltac2" "scheme_kind_rew".
(** Right-to-left rewriting scheme. *)

Ltac2 @ external rew_dep : kind
:= "rocq-runtime.plugins.ltac2" "scheme_kind_rew_dep".
(** Right-to-left dependent rewriting scheme. *)

Ltac2 @ external rew_fwd_dep : kind
:= "rocq-runtime.plugins.ltac2" "scheme_kind_rew_fwd_dep".
(** Right-to-left forward dependent rewriting scheme. *)

Ltac2 @ external rew_r : kind
:= "rocq-runtime.plugins.ltac2" "scheme_kind_rew_r".
(** Left-to-right rewriting scheme. *)

Ltac2 @ external rew_r_dep : kind
:= "rocq-runtime.plugins.ltac2" "scheme_kind_rew_r_dep".
(** Left-to-right dependent rewriting scheme. *)

Ltac2 @ external rew_fwd_r_dep : kind
:= "rocq-runtime.plugins.ltac2" "scheme_kind_rew_fwd_r_dep".
(** Left-to-right forward dependent rewriting scheme. *)

Ltac2 @ external congr : kind
:= "rocq-runtime.plugins.ltac2" "scheme_kind_congr".
(** Congruence scheme. *)

(** {2 Boolean equality and decidability schemes} *)

Ltac2 @ external beq : kind
:= "rocq-runtime.plugins.ltac2" "scheme_kind_beq".
(** Boolean equality scheme. *)

Ltac2 @ external dec_bl : kind
:= "rocq-runtime.plugins.ltac2" "scheme_kind_dec_bl".
(** Boolean to Leibniz equality scheme. *)

Ltac2 @ external dec_lb : kind
:= "rocq-runtime.plugins.ltac2" "scheme_kind_dec_lb".
(** Leibniz to boolean equality scheme. *)

Ltac2 @ external eq_dec : kind
:= "rocq-runtime.plugins.ltac2" "scheme_kind_eq_dec".
(** Decidable equality scheme. *)
