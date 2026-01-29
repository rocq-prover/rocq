(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ltac2.Init.

(** Abstract type representing a transparency state. A transparency state
    is a set of variables, constants, and primitive projections.  *)
Ltac2 Type t.

(** [empty] is the empty transparency state (all constants are opaque). *)
Ltac2 @ external empty : t :=
  "rocq-runtime.plugins.ltac2" "empty_transparent_state".

(** [full] is the full transparency state (all constants are transparent). *)
Ltac2 @ external full : t :=
  "rocq-runtime.plugins.ltac2" "full_transparent_state".

(** [current ()] gives the transparency state of the goal, which is influenced
    by, e.g., the [Strategy] command, or the [with_strategy] Ltac tactic. *)
Ltac2 @ external current : unit -> t :=
  "rocq-runtime.plugins.ltac2" "current_transparent_state".

(** [union t1 t2] builds a transparency state containing all the variables,
    constants, and primitive projections which are either in [t1] or in [t2]. *)
Ltac2 @ external union : t -> t -> t :=
  "rocq-runtime.plugins.ltac2" "union_transparent_state".

(** [inter t1 t2] builds a transparency state containing all the variables,
    constants, and primitive projections which are both in [t1] and in [t2]. *)
Ltac2 @ external inter : t -> t -> t :=
  "rocq-runtime.plugins.ltac2" "inter_transparent_state".

(** [diff t1 t2] builds a transparency state containing all the variables,
    constants, and primitive projections which are in [t1] but not in [t2]. *)
Ltac2 @ external diff : t -> t -> t :=
  "rocq-runtime.plugins.ltac2" "diff_transparent_state".

(** [add_constant c t] adds the constant [c] to the transparency state [t].
    Does nothing if the constant is already present. *)
Ltac2 @ external add_constant : constant -> t -> t :=
  "rocq-runtime.plugins.ltac2" "add_constant_transparent_state".

(** [add_proj p t] adds the primitive projection [p] to the transparency
    state [t]. Does nothing if the projection is already present. *)
Ltac2 @ external add_proj : projection -> t -> t :=
  "rocq-runtime.plugins.ltac2" "add_proj_transparent_state".

(** [add_var p t] adds the local variable [v] to the transparency state [t].
    Does nothing if the variable is already present. *)
Ltac2 @ external add_var : ident -> t -> t :=
  "rocq-runtime.plugins.ltac2" "add_var_transparent_state".

(** [remove_constant c t] removes the constant [c] from the transparency
    state [t]. Does nothing if the constant is not present. *)
Ltac2 @ external remove_constant : constant -> t -> t :=
  "rocq-runtime.plugins.ltac2" "remove_constant_transparent_state".

(** [remove_proj p t] removes the primitive projection [p] from the
    transparency state [t]. Does nothing if the projection is not present. *)
Ltac2 @ external remove_proj : projection -> t -> t :=
  "rocq-runtime.plugins.ltac2" "remove_proj_transparent_state".

(** [remove_var p t] removes the local variable [v] from the transparency
    state [t]. Does nothing if the variable is not present. *)
Ltac2 @ external remove_var : ident -> t -> t :=
  "rocq-runtime.plugins.ltac2" "remove_var_transparent_state".

(** [mem_constant c t] checks whether the constant [c] is present in the
    transparency state [t]. *)
Ltac2 @ external mem_constant : constant -> t -> bool :=
  "rocq-runtime.plugins.ltac2" "mem_constant_transparent_state".

(** [mem_proj p t] checks whether the primitive projection [p] is present in the
    transparency state [t]. *)
Ltac2 @ external mem_proj : projection -> t -> bool :=
  "rocq-runtime.plugins.ltac2" "mem_proj_transparent_state".

(** [mem_var v t] checks whether the local variable [v] is present in the
    transparency state [t]. *)
Ltac2 @ external mem_var : ident -> t -> bool :=
  "rocq-runtime.plugins.ltac2" "mem_var_transparent_state".
