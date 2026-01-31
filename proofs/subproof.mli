(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val refine_by_tactic
  :  name:Names.Id.t
  -> poly:PolyFlags.t
  -> Environ.env
  -> Evd.evar_map
  -> EConstr.types
  -> unit Proofview.tactic
  -> EConstr.constr * Evd.evar_map
(** A variant of {!Proof.solve} that handles open terms as well.
    Caveat: all effects are purged in the returned term at the end, but other
    evars solved by side-effects are NOT purged, so that unexpected failures may
    occur. Ideally all code using this function should be rewritten in the
    monad. *)

val build_by_tactic :
  Environ.env ->
  uctx:UState.t -> poly:PolyFlags.t ->
  typ:EConstr.types ->
  unit Proofview.tactic ->
  Constr.constr * Constr.types * UState.named_universes_entry * UState.t
(** Semantics of this function is a bit dubious, use with care *)

val build_by_tactic_opt :
  Environ.env ->
  uctx:UState.t -> poly:PolyFlags.t ->
  typ:EConstr.types ->
  unit Proofview.tactic ->
  (Constr.constr * Constr.types * UState.named_universes_entry * UState.t) option
(** Same as above but returns None rather than an exception if the proof is not finished *)

val declare_abstract :
  name:Names.Id.t ->
  poly:PolyFlags.t ->
  sign:EConstr.named_context ->
  secsign:Environ.named_context_val ->
  opaque:bool ->
  solve_tac:unit Proofview.tactic ->
  Environ.env ->
  Evd.evar_map ->
  EConstr.t -> Evd.evar_map * EConstr.t * EConstr.t list * bool

val shrink_entry :
  ('a, 'b, 'c) Context.Named.Declaration.pt list ->
  Constr.constr ->
  Constr.types -> Constr.constr * Constr.constr * EConstr.t list
