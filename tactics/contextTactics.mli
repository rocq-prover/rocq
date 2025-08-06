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
open Environ
open Evd
open Evarutil

(** Tactics which modify the local context (clear, move, rename, ...). *)

(** [clear ?fail ids] removes hypotheses [ids] from the context.
    - [fail]: function which is called if clearing the hypotheses leads to a dependency error.
      By default [fail] throws the [ClearDependency] exception. *)
val clear :
  ?fail:(env -> evar_map -> Id.t -> clear_dependency_error -> GlobRef.t option ->
         evar_map * named_context_val * EConstr.t) ->
  Id.t list ->
  unit Proofview.tactic

val clear_wildcards : Names.lident list -> unit Proofview.tactic

(** [clear_body ids] removes the definitions (but not the declarations) of hypotheses [ids]
    from the context. *)
val clear_body : Id.t list -> unit Proofview.tactic

(** [keep ids] clears every hypothesis except:
    - The hypotheses in [ids].
    - The hypotheses which occur in the conclusion.
    - The hypotheses which occur in the type or body of a kept hypothesis. *)
val keep : Id.t list -> unit Proofview.tactic

(** [move_hyp id loc] moves hypothesis [id] to location [loc]. *)
val move_hyp : Id.t -> Id.t Logic.move_location -> unit Proofview.tactic

(** [rename_hyp [(x1, y1); (x2; y2); ...]] renames hypotheses [xi] into [yi].
    - The names [x1, x2, ...] are expected to be distinct.
    - The names [y1, y2, ...] are expected to be distinct. *)
val rename_hyp : (Id.t * Id.t) list -> unit Proofview.tactic
