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
open EConstr

(** Tactics which build fixpoints and cofixpoints. *)

(** [fix f idx] refines the goal using a fixpoint.
    - [f] is the name of the variable which represents the fixpoint.
    - [idx] is the index of the structurally recursive argument (starting at 1). *)
val fix : Id.t -> int -> unit Proofview.tactic

(** [mutual_fix f idx fs] refines the goal using a mutual fixpoint.
    - [f] and [idx] are the name and recursive argument index for the first fixpoint.
      The type of [f] is simply the conclusion of the goal.
    - [fs] contains the name, recursive argument index, and type of every other fixpoint
      in the mutual block. *)
val mutual_fix :
  Id.t -> int -> (Id.t * int * constr) list -> unit Proofview.tactic

(** [cofix f] refines the goal using a cofixpoint.
    - [f] is the name of the variable which represents the cofixpoint. *)
val cofix : Id.t -> unit Proofview.tactic

(** [mutual_cofix f fs] refines the goal using a mutual cofixpoint.
    - [f] is the name of the first cofixpoint. The type of [f] is simply the conclusion of the goal.
    - [fs] contains the name and type of every other cofixpoint in the mutual block. *)
val mutual_cofix : Id.t -> (Id.t * constr) list -> unit Proofview.tactic
