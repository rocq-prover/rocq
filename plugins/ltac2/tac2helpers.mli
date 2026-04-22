(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val ltac2_plugin : string

val define :
  ?plugin:string ->
  string ->
  ('a, 'b) Tac2externals.spec ->
  'b ->
  unit

val thaw : (unit -> 'a Proofview.tactic) -> 'a Proofview.tactic
val uthaw : 'a Tac2ffi.repr -> Tac2val.valexpr -> 'a Proofview.tactic
val return : 'a -> 'a Proofview.tactic

val fatal_flag : unit Exninfo.t
val has_fatal_flag : Exninfo.info -> bool

val set_bt : Exninfo.info -> Exninfo.info Proofview.tactic
val throw : ?info:Exninfo.info -> exn -> 'a Proofview.tactic
val fail : ?info:Exninfo.info -> exn -> 'a Proofview.tactic

val wrap_exceptions :
  ?passthrough:bool ->
  (unit -> 'a Proofview.tactic) ->
  'a Proofview.tactic

val pf_apply :
  ?catch_exceptions:bool ->
  (Environ.env -> Evd.evar_map -> 'a Proofview.tactic) ->
  'a Proofview.tactic

val assert_focussed : unit Proofview.tactic
