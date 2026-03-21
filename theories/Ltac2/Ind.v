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

Ltac2 Type t := inductive.
(** An [inductive] is a name of a mutually inductive type and the index of an
    inductive block within that type. *)

Ltac2 @ external equal : t -> t -> bool := "rocq-runtime.plugins.ltac2" "ind_equal".
(** Equality test. *)

Ltac2 Type data.
(** The actual data specified by a concrete declaration of an inductive type,
    containing, e.g., its constructors and its parameters. A value of type
    [data] corresponds to one inductive type within a larger mutually inductive
    block. *)

Ltac2 @ external data : t -> data := "rocq-runtime.plugins.ltac2" "ind_data".
(** Get the value named by [t] in the current environment. Panics if [t] is not
    in the current environment. *)

Ltac2 @ external repr : data -> t := "rocq-runtime.plugins.ltac2" "ind_repr".
(** Returns the name of the inductive type corresponding to the block. Inverse
    of [data]. *)

Ltac2 @ external index : t -> int := "rocq-runtime.plugins.ltac2" "ind_index".
(** Returns the index of the inductive type inside its mutual block. Guaranteed
    to range between [0] and [nblocks data - 1] where [data] was retrieved using
    the above function. *)

Ltac2 @ external nblocks : data -> int := "rocq-runtime.plugins.ltac2" "ind_nblocks".
(** Returns the number of inductive types appearing in a mutual block. *)

Ltac2 @ external nconstructors : data -> int := "rocq-runtime.plugins.ltac2" "ind_nconstructors".
(** Returns the number of constructors appearing in the current block. *)

Ltac2 @ external get_block : data -> int -> data := "rocq-runtime.plugins.ltac2" "ind_get_block".
(** [get_block data n] is the block corresponding to the nth inductive type in
    [data]'s parent mutually inductive type. Index must range between [0] and
    [nblocks data - 1], otherwise the function panics. *)

Ltac2 @ external get_constructor : data -> int -> constructor := "rocq-runtime.plugins.ltac2" "ind_get_constructor".
(** Returns the nth constructor of the inductive type. Index must range between
    [0] and [nconstructors data - 1], otherwise the function panics. *)

Ltac2 @ external nparams : data -> int := "rocq-runtime.plugins.ltac2" "ind_get_nparams".
(** The number of parameters of the inductive type, including both uniform and
    non-uniform parameters. Does not count local let-ins. *)

Ltac2 @ external nparams_uniform : data -> int := "rocq-runtime.plugins.ltac2" "ind_get_nparams_rec".
(** The number of recursively uniform (i.e., ordinary) parameters of the
    inductive type. *)

Ltac2 @ external get_projections : data -> projection array option
  := "rocq-runtime.plugins.ltac2" "ind_get_projections".
(** Returns the list of projections for a primitive record,
    or [None] if the inductive is not a primitive record. *)

Ltac2 @ external constructor_nargs : data -> int array := "rocq-runtime.plugins.ltac2" "constructor_nargs".
(** [Array.get (constructor_nargs data) n] is the number of non-parameter
    arguments accepted by the [n]th constructor of this inductive type. Add
    [Array.get (constructor_nargs data) n] to [Ind.nparams_data] to get the total
    number of arguments of the constructor. *)

Ltac2 @ external constructor_ndecls : data -> int array := "rocq-runtime.plugins.ltac2" "constructor_ndecls".
(** [Array.get (constructor_ndecls data) n] is the number of variables bound in
    a pattern match expression by the [n]th constructor of this inductive type.
    Can be greater than [constructor_nargs] if the constructors have local
    let-bindings, e.g., applied to [Inductive Ind (A : Type) (f : A -> A) : Set
    := Constr (x : A) (y := f x)] it would return [[|2|]], because in [match t
    with Constr _ _ x y => e end], [x] and [y] are bound in [e]. *)

Ltac2 @external print : t -> message
  := "rocq-runtime.plugins.ltac2" "ind_print".
(** Print the inductive using the shortest qualified identifier which refers to it.
    Does not avoid variable names in the current or global environment. *)

(** {2 Scheme lookup} *)

Ltac2 Type scheme_kind.
(** An abstract type representing a scheme kind. Use the predefined values
    below to refer to specific scheme kinds. *)

Ltac2 @ external scheme_lookup : scheme_kind -> t -> Std.reference option
  := "rocq-runtime.plugins.ltac2" "ind_scheme_lookup".
(** [scheme_lookup kind ind] looks up the scheme registered under [kind] for
    inductive [ind]. Returns [None] if no such scheme is registered. *)

(** {3 Elimination schemes} *)

Ltac2 @ external rect_dep : scheme_kind
  := "rocq-runtime.plugins.ltac2" "ind_scheme_kind_rect_dep".
(** Dependent recursion scheme for Type. *)

Ltac2 @ external rec_dep : scheme_kind
  := "rocq-runtime.plugins.ltac2" "ind_scheme_kind_rec_dep".
(** Dependent recursion scheme for Set. *)

Ltac2 @ external ind_dep : scheme_kind
  := "rocq-runtime.plugins.ltac2" "ind_scheme_kind_ind_dep".
(** Dependent induction scheme for Prop. *)

Ltac2 @ external sind_dep : scheme_kind
  := "rocq-runtime.plugins.ltac2" "ind_scheme_kind_sind_dep".
(** Dependent induction scheme for SProp. *)

Ltac2 @ external rect_nodep : scheme_kind
  := "rocq-runtime.plugins.ltac2" "ind_scheme_kind_rect_nodep".
(** Non-dependent recursion scheme for Type. *)

Ltac2 @ external rec_nodep : scheme_kind
  := "rocq-runtime.plugins.ltac2" "ind_scheme_kind_rec_nodep".
(** Non-dependent recursion scheme for Set. *)

Ltac2 @ external ind_nodep : scheme_kind
  := "rocq-runtime.plugins.ltac2" "ind_scheme_kind_ind_nodep".
(** Non-dependent induction scheme for Prop. *)

Ltac2 @ external sind_nodep : scheme_kind
  := "rocq-runtime.plugins.ltac2" "ind_scheme_kind_sind_nodep".
(** Non-dependent induction scheme for SProp. *)

(** {3 Case analysis schemes} *)

Ltac2 @ external case_dep : scheme_kind
  := "rocq-runtime.plugins.ltac2" "ind_scheme_kind_case_dep".
(** Dependent case analysis scheme for Type. *)

Ltac2 @ external case_nodep : scheme_kind
  := "rocq-runtime.plugins.ltac2" "ind_scheme_kind_case_nodep".
(** Non-dependent case analysis scheme for Type. *)

Ltac2 @ external casep_dep : scheme_kind
  := "rocq-runtime.plugins.ltac2" "ind_scheme_kind_casep_dep".
(** Dependent case analysis scheme for Prop. *)

Ltac2 @ external casep_nodep : scheme_kind
  := "rocq-runtime.plugins.ltac2" "ind_scheme_kind_casep_nodep".
(** Non-dependent case analysis scheme for Prop. *)

(** {3 Equality schemes} *)

Ltac2 @ external sym : scheme_kind
  := "rocq-runtime.plugins.ltac2" "ind_scheme_kind_sym".
(** Symmetry scheme. *)

Ltac2 @ external sym_involutive : scheme_kind
  := "rocq-runtime.plugins.ltac2" "ind_scheme_kind_sym_involutive".
(** Involutive symmetry scheme. *)

Ltac2 @ external rew : scheme_kind
  := "rocq-runtime.plugins.ltac2" "ind_scheme_kind_rew".
(** Right-to-left rewriting scheme. *)

Ltac2 @ external rew_dep : scheme_kind
  := "rocq-runtime.plugins.ltac2" "ind_scheme_kind_rew_dep".
(** Right-to-left dependent rewriting scheme. *)

Ltac2 @ external rew_fwd_dep : scheme_kind
  := "rocq-runtime.plugins.ltac2" "ind_scheme_kind_rew_fwd_dep".
(** Right-to-left forward dependent rewriting scheme. *)

Ltac2 @ external rew_r : scheme_kind
  := "rocq-runtime.plugins.ltac2" "ind_scheme_kind_rew_r".
(** Left-to-right rewriting scheme. *)

Ltac2 @ external rew_r_dep : scheme_kind
  := "rocq-runtime.plugins.ltac2" "ind_scheme_kind_rew_r_dep".
(** Left-to-right dependent rewriting scheme. *)

Ltac2 @ external rew_fwd_r_dep : scheme_kind
  := "rocq-runtime.plugins.ltac2" "ind_scheme_kind_rew_fwd_r_dep".
(** Left-to-right forward dependent rewriting scheme. *)

Ltac2 @ external congr : scheme_kind
  := "rocq-runtime.plugins.ltac2" "ind_scheme_kind_congr".
(** Congruence scheme. *)

(** {3 Boolean equality and decidability schemes} *)

Ltac2 @ external beq : scheme_kind
  := "rocq-runtime.plugins.ltac2" "ind_scheme_kind_beq".
(** Boolean equality scheme. *)

Ltac2 @ external dec_bl : scheme_kind
  := "rocq-runtime.plugins.ltac2" "ind_scheme_kind_dec_bl".
(** Boolean to Leibniz equality scheme. *)

Ltac2 @ external dec_lb : scheme_kind
  := "rocq-runtime.plugins.ltac2" "ind_scheme_kind_dec_lb".
(** Leibniz to boolean equality scheme. *)

Ltac2 @ external eq_dec : scheme_kind
  := "rocq-runtime.plugins.ltac2" "ind_scheme_kind_eq_dec".
(** Decidable equality scheme. *)
