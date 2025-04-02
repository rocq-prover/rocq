(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Univ
open Quality

type t = ElimConstraints.t * UnivConstraints.t

type poly_constraints = t

val make : ElimConstraints.t -> UnivConstraints.t -> t

val empty : t
val is_empty : t -> bool

val equal : t -> t -> bool

val qualities : t -> ElimConstraints.t

val univs : t -> UnivConstraints.t

val of_qualities : ElimConstraints.t -> t

val of_univs : UnivConstraints.t -> t

val set_qualities : ElimConstraints.t -> t -> t

val set_univs : UnivConstraints.t -> t -> t

val add_quality : ElimConstraint.t -> t -> t

val add_univ : UnivConstraint.t -> t -> t

val union : t -> t -> t

val diff : t -> t -> t

val elements : t -> ElimConstraint.t list * UnivConstraint.t list

val filter_qualities : (ElimConstraints.elt -> bool) -> t -> t
val filter_univs : (UnivConstraints.elt -> bool) -> t -> t

val pr : (QVar.t -> Pp.t) -> (Level.t -> Pp.t) -> t -> Pp.t

val hcons : t Hashcons.f

type 'a constrained = 'a * t

val constraints_of : 'a constrained -> t

type 'a constraint_function = 'a -> 'a -> t -> t

val enforce_eq_univ : Level.t constraint_function

val enforce_leq_univ : Level.t constraint_function

val enforce_eq_quality : Quality.t constraint_function

val enforce_elim_to : Quality.t constraint_function

val fold : (ElimConstraint.t -> 'a -> 'a) * (UnivConstraint.t -> 'b -> 'b) -> t
  -> ('a * 'b) -> ('a * 'b)

(** Polymorphic contexts (as sets) *)

(** A set of qualities and universes with polymorphic PolyConstraints.t.
    We linearize the set to a list after typechecking.
    Beware, representation could change.
*)

module ContextSet :
sig
  type t = Level.Set.t constrained

  val empty : t
  val is_empty : t -> bool

  val singleton_lvl : Level.t -> t
  val of_lvl_set : Level.Set.t -> t

  val equal : t -> t -> bool
  val union : t -> t -> t

  val append : t -> t -> t
  (** Variant of {!union} which is more efficient when the left argument is
      much smaller than the right one. *)

  val diff : t -> t -> t
  val add_level : Level.t -> t -> t
  val add_constraints : poly_constraints -> t -> t
  val add_univ_constraints : UnivConstraints.t -> t -> t
  val add_elim_constraints : ElimConstraints.t -> t -> t
  val filter_out_constant_qualities : t -> t

  val constraints : t -> poly_constraints
  val univ_constraints : t -> UnivConstraints.t
  val elim_constraints : t -> ElimConstraints.t
  val levels : t -> Level.Set.t

  val size : t -> int
  (** The number of universes in the context *)

  val pr : (QVar.t -> Pp.t) -> (Level.t -> Pp.t) -> t -> Pp.t

  val hcons : t Hashcons.f
end

type 'a in_poly_context_set = 'a * ContextSet.t
