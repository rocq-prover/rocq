(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Decl_kinds

(* Declaration hooks *)
type declaration_hook

val mk_hook : (Decl_kinds.locality -> GlobRef.t -> unit) -> declaration_hook
val call_hook :
  ?hook:declaration_hook -> ?fix_exn:Future.fix_exn ->
  Decl_kinds.locality -> GlobRef.t -> unit

(* Proofs that define a constant + terminators *)
type t
type proof_terminator

val universe_proof_terminator :
  ?univ_hook:(UState.t option -> declaration_hook) ->
  Proof_global.lemma_possible_guards ->
  proof_terminator

val standard_proof_terminator :
  ?hook:declaration_hook -> Proof_global.lemma_possible_guards ->
  proof_terminator

val pf_map : (Proof_global.t -> Proof_global.t) -> t -> t
val pf_fold : (Proof_global.t -> 'a) -> t -> 'a

val by : unit Proofview.tactic -> t -> t * bool

val get_all_proof_names : t -> Names.Id.t list

val discard : Names.lident -> t -> t option
val discard_current : t -> t option

val with_current_proof :
  (unit Proofview.tactic -> Proof.t -> Proof.t * 'a) -> t -> t * 'a

val simple_with_current_proof :
  (unit Proofview.tactic -> Proof.t -> Proof.t) -> t -> t

(* Start of high-level proofs with an associated constant *)

val start_proof
  :  ontop:t option
  -> Id.t
  -> ?pl:UState.universe_decl
  -> goal_kind
  -> Evd.evar_map
  -> ?terminator:(?hook:declaration_hook -> Proof_global.lemma_possible_guards -> proof_terminator)
  -> ?sign:Environ.named_context_val
  -> ?compute_guard:Proof_global.lemma_possible_guards
  -> ?hook:declaration_hook
  -> EConstr.types
  -> t

val start_dependent_proof
  :  ontop:t option
  -> Id.t
  -> ?pl:UState.universe_decl
  -> goal_kind
  -> ?terminator:(?hook:declaration_hook -> Proof_global.lemma_possible_guards -> proof_terminator)
  -> ?sign:Environ.named_context_val
  -> ?compute_guard:Proof_global.lemma_possible_guards
  -> ?hook:declaration_hook
  -> Proofview.telescope
  -> t

val start_proof_univs
  :  ontop:t option
  -> Id.t
  -> ?pl:UState.universe_decl
  -> goal_kind
  -> Evd.evar_map
  -> ?terminator:(?univ_hook:(UState.t option -> declaration_hook) -> Proof_global.lemma_possible_guards -> proof_terminator)
  -> ?sign:Environ.named_context_val
  -> ?compute_guard:Proof_global.lemma_possible_guards
  -> ?univ_hook:(UState.t option -> declaration_hook) -> EConstr.types -> t

val start_proof_com
  :  program_mode:bool
  -> ontop:t option
  -> ?inference_hook:Pretyping.inference_hook
  -> ?hook:declaration_hook -> goal_kind -> Vernacexpr.proof_expr list
  -> t

val start_proof_with_initialization
  :  ontop:t option
  -> ?hook:declaration_hook
  -> goal_kind -> Evd.evar_map -> UState.universe_decl
  -> (bool * Proof_global.lemma_possible_guards * unit Proofview.tactic list option) option
  -> (Id.t (* name of thm *) *
     (EConstr.types (* type of thm *) *
      (Name.t list (* names to pre-introduce *) * Impargs.manual_explicitation list))) list
  -> int list option
  -> t

val fresh_name_for_anonymous_theorem : pstate:t option -> Id.t

(* Prepare global named context for proof session: remove proofs of
   opaque section definitions and remove vm-compiled code *)

val initialize_named_context_for_proof : unit -> Environ.named_context_val

(** {6 Saving proofs } *)

val save_proof_admitted
  :  ?proof:(Proof_global.proof_object * proof_terminator)
  -> pstate:t
  -> unit

val save_proof_proved
  :  ?proof:(Proof_global.proof_object * proof_terminator)
  -> ?pstate:t
  -> opaque:Proof_global.opacity_flag
  -> idopt:Names.lident option
  -> t option

(* API to build a terminator, should go away *)
type proof_ending =
  | Admitted of Names.Id.t * Decl_kinds.goal_kind * Entries.parameter_entry * UState.t
  | Proved of Proof_global.opacity_flag *
              Names.lident option *
              Proof_global.proof_object

val make_terminator : (proof_ending -> unit) -> proof_terminator
val apply_terminator : proof_terminator -> proof_ending -> unit
val copy_terminators : src:t -> tgt:t -> t
(** Gets the current terminator without checking that the proof has
    been completed. Useful for the likes of [Admitted]. *)

val get_terminator : t -> proof_terminator
val set_terminator : proof_terminator -> t -> t
