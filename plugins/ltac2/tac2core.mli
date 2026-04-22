(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val throw : ?info:Exninfo.info -> exn -> 'a Proofview.tactic

(** [catch_exceptions] default false *)
val pf_apply : ?catch_exceptions:bool -> (Environ.env -> Evd.evar_map -> 'a Proofview.tactic) -> 'a Proofview.tactic

(** Adds ltac2 backtrace. With [passthrough:false] (default), acts
    like [Proofview.wrap_exceptions] + Ltac2 backtrace handling. *)
val wrap_exceptions : ?passthrough:bool -> (unit -> 'a Proofview.tactic) -> 'a Proofview.tactic

val constr_flags : Pretyping.inference_flags
val open_constr_no_classes_flags : Pretyping.inference_flags
val preterm_flags : Pretyping.inference_flags
