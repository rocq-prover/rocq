(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Tac2ffi
open Tac2types

val make_to_repr : (Tac2val.valexpr -> 'a) -> 'a Tac2ffi.repr

val qhyp : quantified_hypothesis repr

val bindings : bindings repr

val constr_with_bindings : constr_with_bindings repr

val format : format list repr

val rewrite_result : Rewrite.rewrite_result repr
