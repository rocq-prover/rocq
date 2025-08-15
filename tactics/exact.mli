(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open EConstr

(** Tactics which solve the goal (e.g. [assumption]) or insert a cast. *)

(** [assumption] solves the goal if it is convertible to the type of a hypothesis.
    Fails if there is no such hypothesis. *)
val assumption : unit Proofview.tactic

(** [exact_no_check x] solves the goal with term [x].
    It does not check that the type of [x] is convertible to the conclusion. *)
val exact_no_check : constr -> unit Proofview.tactic

(** [exact_check x] solves the goal with term [x].
    Fails if the type of [x] does not match the conclusion. *)
val exact_check : constr -> unit Proofview.tactic

(** [exact_proof x] internalizes the constr_expr [x] using the conclusion,
    and solves the goal using the internalized term.
    Fails if [x] could not be internalized. *)
val exact_proof : Constrexpr.constr_expr -> unit Proofview.tactic

(** [cast_no_check ~kind new_concl] changes the conclusion to [new_concl] by inserting a cast
    of kind [kind]. It does not check that the new conclusion is indeed convertible to the old
    conclusion. *)
val cast_no_check : kind:cast_kind -> constr -> unit Proofview.tactic

(** Specialization of [cast_no_check] to [VMcast]. *)
val vm_cast_no_check : constr -> unit Proofview.tactic

(** Specialization of [cast_no_check] to [NATIVEcast]. *)
val native_cast_no_check : constr -> unit Proofview.tactic
