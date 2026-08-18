(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type opaques

val set_indirect_accessor : (Opaqueproof.opaque -> Opaqueproof.opaque_proofterm) -> unit

val compile_module_bytecode : Environ.env -> Vmlibrary.t -> Names.ModPath.t ->
  'a Mod_declarations.generic_module_body ->
  Vmlibrary.t * 'a Mod_declarations.generic_module_body
(** Recompile the VM bytecode of every constant of a module (type) body from its
    body, discarding whatever code the [.vo] file claims, and add it to the given
    table. *)

val check_module : Environ.env -> opaques -> Retroknowledge.action list -> Names.ModPath.t -> Mod_declarations.module_body -> opaques

exception BadConstant of Names.Constant.t * Pp.t

val constants_of_opaques : Environ.env -> opaques -> Names.Constant.t list
val empty_opaques : opaques
