(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Declarations
open Cooking
open Constr

val cook_opaque_proofterm : cooking_info list ->
  Opaqueproof.opaque_proofterm -> Opaqueproof.opaque_proofterm

(** The proof term {!cook_opaque_proofterm} gives, built with
    {!Cooking.abstract_as_body_shared}, so that expanding the section's
    context in it keeps the sharing of the stored term where the memo holds
    it. *)
val cook_opaque_proofterm_shared : cooking_info list ->
  Opaqueproof.opaque_proofterm -> Opaqueproof.opaque_proofterm

val cook_constant :
  Environ.env -> cooking_info -> constant_body -> (Opaqueproof.opaque, unit) pconstant_body

val cook_inductive :
  cooking_info -> mutual_inductive_body -> mutual_inductive_body

val cook_rel_context : cooking_info -> rel_context -> rel_context
