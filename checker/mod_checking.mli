(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
open Names

type axioms = private {
  undef : KerName.Set.t;
  unsafe_flags : CheckFlags.unsafe_flags KerName.Map.t;
}

val set_indirect_accessor : (Opaqueproof.opaque -> Opaqueproof.opaque_proofterm) -> unit

val check_module : Environ.env -> Retroknowledge.action list -> Names.ModPath.t -> Mod_declarations.module_body -> unit

exception BadConstant of Names.Constant.t * Pp.t

val empty_axioms : axioms

val is_axiom_free : Environ.env -> axioms -> bool

(** Record assumptions hidden by module signatures without type checking. *)
val collect_library_axioms : axioms -> Safe_typing.compiled_library -> axioms
