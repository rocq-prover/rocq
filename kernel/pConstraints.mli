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
open Sorts

type t = ElimConstraints.t * UnivConstraints.t

type pconstraints = t
(** Stands for prenex sort poly constraints *)

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

val pr : Sorts.printer -> t -> Pp.t

val hcons : t Hashcons.f

type 'a constrained = 'a * t

val constraints_of : 'a constrained -> t

type 'a constraint_function = 'a -> 'a -> t -> t

val enforce_eq_univ : Level.t constraint_function

val enforce_leq_univ : Level.t constraint_function

val enforce_elim_to : Quality.t constraint_function

val fold : (ElimConstraint.t -> 'a -> 'a) * (UnivConstraint.t -> 'b -> 'b) -> t
  -> ('a * 'b) -> ('a * 'b)
