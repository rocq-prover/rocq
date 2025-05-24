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
Require Ltac2.TransparentState.


(** This file contains conversion and unification.
    Both can modify universe constrains.
    Unification can additionaly unify evariables.
*)


(** Conversion  *)

Ltac2 Type conv_flag := [
| CONV
| CUMUL
].
(** Controls if cumulativity Prop <= Set <= Type 1 <= ... <= Type i <= ... is used for conversion.
    Cumulativity is useful when generating a new type, for instance through retying,
    and you want to compare it up to conversion with a specific existing type.
*)

Ltac2 @ external conv : conv_flag -> TransparentState.t -> constr -> constr -> bool := "rocq-runtime.plugins.ltac2" "infer_conv".
(** Conv returns true if both terms are convertible, in which case it updates the
    environment with the universes constraints required for the terms to be convertible.
    It returns false if the terms are not convertible.
    It fails if there is more than one goal under focus.

    Conv is parametrised by:
    - conv_flag which controls if conversion is done up to cumulativity or not
    - TransparentState.t which controls which constants get unfolded during conversion
*)

Ltac2 conv_current : constr -> constr -> bool := fun c1 c2 => conv CONV (TransparentState.current ()) c1 c2.
(** It only unfolds constants that are transparent in the current state *)

Ltac2 conv_full : constr -> constr -> bool := fun c1 c2 => conv CONV TransparentState.full c1 c2.
(** All constants are considered as transparents when doing conversion *)

(** Unification *)

(** [unify ts c1 c2] unifies [c1] and [c2] (using Evarconv unification), which
    may have the effect of instantiating evars. If the [c1] and [c2] cannot be
    unified, an [Internal] exception is raised. *)
Ltac2 @ external unify : TransparentState.t -> constr -> constr -> unit :=
  "rocq-runtime.plugins.ltac2" "evarconv_unify".

(** [unify_with_full_ts] is like [unify TransparentState.full]. *)
Ltac2 unify_with_full_ts : constr -> constr -> unit := fun c1 c2 =>
  unify TransparentState.full c1 c2.

(** [unify_with_current_ts] is like [unify (TransparentState.current ())]. *)
Ltac2 unify_with_current_ts : constr -> constr -> unit := fun c1 c2 =>
  unify (TransparentState.current ()) c1 c2.
