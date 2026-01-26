(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Mod_subst
open Tac2expr

val subst_type : substitution -> 'a glb_typexpr -> 'a glb_typexpr
val subst_expr : substitution -> glb_tacexpr -> glb_tacexpr
val subst_quant_typedef : substitution -> glb_quant_typedef -> glb_quant_typedef
val subst_type_scheme : substitution -> type_scheme -> type_scheme

val subst_rawexpr : substitution -> raw_tacexpr -> raw_tacexpr
