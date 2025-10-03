(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Declare ML Module "rocq-runtime.plugins.ltac".

#[export] Set Default Proof Mode "Classic".

(** Forward declaration for ltac2. *)
Ltac easy_forward_decl := fail "Cannot use easy: Corelib.Init.Tactics not loaded".

Module Internal.
  (** Export some tactics for internal (Corelib) use.

      These tactics are declared as "local" in the plugin, so they
      exist with name Ltac.foo while in this file and this module
      reexports them. *)

  Ltac head_of_constr id c := Ltac.head_of_constr id c.

End Internal.
