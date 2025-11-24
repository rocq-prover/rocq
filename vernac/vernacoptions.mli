(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Goptions

val vernac_set_option :
  'summary_mut ->
  locality:option_locality ->
  stage:(_,'summary_mut) Summary.StageG.t ->
  option_name -> Vernacexpr.option_setting ->
  unit

val vernac_add_option :
  Summary.Interp.mut -> Libobject.locality -> option_name -> table_value list -> unit

val vernac_remove_option :
  Summary.Interp.mut -> Libobject.locality -> option_name -> table_value list -> unit

val vernac_mem_option : option_name -> table_value list -> unit

val vernac_print_option : Summary.Interp.t ->
  option_name -> unit
