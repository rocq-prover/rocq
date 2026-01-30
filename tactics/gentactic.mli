(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names

(** Generic tactic expressions.
    Internally implemented using [Genarg]. *)

type raw_generic_tactic

type glob_generic_tactic

type ('raw, 'glob) tag

val make : string -> ('raw, 'glb) tag
(** Each declared tag must be registered using all the following [register] functions
    (except when the callback cannot be called ie when the value type at that level is empty). *)

val empty : (Empty.t, Empty.t) tag

val of_raw : ('raw,_) tag -> 'raw -> raw_generic_tactic

val register_print : ('raw, 'glb) tag -> 'raw Genprint.printer -> 'glb Genprint.printer -> unit

val print_raw : Environ.env -> Evd.evar_map -> ?level:Constrexpr.entry_relative_level ->
  raw_generic_tactic -> Pp.t

val print_glob : Environ.env -> Evd.evar_map -> ?level:Constrexpr.entry_relative_level ->
  glob_generic_tactic -> Pp.t

val register_subst : (_, 'glb) tag -> 'glb Gensubst.subst_fun -> unit

val subst : Mod_subst.substitution -> glob_generic_tactic -> glob_generic_tactic

val register_intern : ('raw, 'glb) tag -> ('raw, 'glb) Genintern.intern_fun -> unit

val intern : ?strict:bool -> Environ.env -> ?ltacvars:Id.Set.t -> raw_generic_tactic -> glob_generic_tactic
(** [strict] is default true *)

val register_interp : (_, 'glb) tag -> (Geninterp.Val.t Id.Map.t -> 'glb -> unit Proofview.tactic) -> unit

val interp : ?lfun:Geninterp.Val.t Id.Map.t -> glob_generic_tactic -> unit Proofview.tactic

val wit_generic_tactic : raw_generic_tactic Genarg.vernac_genarg_type

val to_raw_genarg : raw_generic_tactic -> Genarg.raw_generic_argument
(** For serlib *)
