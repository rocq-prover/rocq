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
open Constr
open Environ
open Univ
open UVars

module QualityOrSet : sig
  type t = Qual of Sorts.Quality.t | Set

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val of_quality : Sorts.Quality.t -> t
  val of_sort : Sorts.t -> t
  val quality : t -> Sorts.Quality.t

  val eliminates_to : t -> t -> bool

  val set : t

  val qtype : t
  val prop : t
  val sprop : t

  val is_type : t -> bool
  val is_set : t -> bool
  val is_prop : t -> bool
  val is_sprop : t -> bool

  val pr : (Sorts.QVar.t -> Pp.t) -> t -> Pp.t
  val raw_pr : t -> Pp.t

  val all_constants : t list
  val all : t list
end

type univ_length_mismatch = {
  gref : GlobRef.t;
  actual : int * int;
  expect : int * int;
}
(* Due to an OCaml bug ocaml/ocaml#10027 inlining this record will cause
compliation with -rectypes to crash. *)
exception UniverseLengthMismatch of univ_length_mismatch

(** Side-effecting functions creating new universe levels. *)

val new_univ_global : unit -> UGlobal.t
val new_sort_global : Id.t -> Sorts.QGlobal.t
val fresh_level : unit -> Level.t
val fresh_sort_quality : unit -> Sorts.QVar.t

(** Build a fresh instance for a given context, its associated substitution and
    the instantiated constraints. *)

(* TODO: move this type and its associated functions somewhere reasonable *)

type sort_context_set = (Sorts.QVar.Set.t * Univ.Level.Set.t) * PConstraints.t

type 'a in_sort_context_set = 'a * sort_context_set

val sort_context_union : sort_context_set -> sort_context_set -> sort_context_set

val empty_sort_context : sort_context_set

val is_empty_sort_context : sort_context_set -> bool

val diff_sort_context : sort_context_set -> sort_context_set -> sort_context_set

val pr_sort_context : (Sorts.QVar.t -> Pp.t) -> (Univ.Level.Set.elt -> Pp.t) ->
  sort_context_set -> Pp.t

val fresh_instance : AbstractContext.t -> Instance.t in_sort_context_set

(** The globref is only used for the error message when there is a mismatch. *)
val fresh_instance_from : ?loc:Loc.t -> AbstractContext.t -> (GlobRef.t * Instance.t) option ->
  Instance.t in_sort_context_set

val fresh_sort_in_quality : QualityOrSet.t -> Sorts.t in_sort_context_set
(** NB: QSort is treated as QType *)

val fresh_constant_instance : env -> Constant.t ->
  pconstant in_sort_context_set
val fresh_inductive_instance : env -> inductive ->
  pinductive in_sort_context_set
val fresh_constructor_instance : env -> constructor ->
  pconstructor in_sort_context_set
val fresh_array_instance : env ->
  Instance.t in_sort_context_set

val fresh_global_instance : ?loc:Loc.t -> ?names:UVars.Instance.t -> env -> GlobRef.t ->
  constr in_sort_context_set

val fresh_sort_context_instance : sort_context_set ->
  sort_level_subst * sort_context_set

(** Create a fresh global in the environment argument, without side effects.
    BEWARE: this raises an error on polymorphic constants/inductives:
    the constraints should be properly added to an evd.
    See Evd.fresh_global, Evarutil.new_global, and pf_constr_of_global for
    the proper way to get a fresh copy of a polymorphic global reference. *)
val constr_of_monomorphic_global : env -> GlobRef.t -> constr

val family_to_str : QualityOrSet.t -> string 
