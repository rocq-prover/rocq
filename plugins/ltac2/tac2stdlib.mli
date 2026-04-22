(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Tac2ffi
open Names

(** Standard tactics sharing their implementation with Ltac1 *)

module Ltac2Std : sig
  type hypothesis = Tac2types.quantified_hypothesis
  type bindings = Tac2types.bindings
  type constr_with_bindings = Tac2types.constr_with_bindings
  type occurrences = Tac2types.occurrences
  type hyp_location_flag = Tac2types.hyp_location_flag
  type clause = Tac2types.clause
  type reference = GlobRef.t
  type strength = Genredexpr.strength
  type red_flags = Tac2types.red_flag
  type intro_pattern = Tac2types.intro_pattern
  and intro_pattern_naming = Tac2types.intro_pattern_naming
  and intro_pattern_action = Tac2types.intro_pattern_action
  and or_and_intro_pattern = Tac2types.or_and_intro_pattern
  type destruction_arg = Tac2types.destruction_arg
  type induction_clause = Tac2types.induction_clause
  type assertion = Tac2types.assertion
  type repeat = Equality.multi
  type orientation = Tac2types.orientation
  type rewriting = Tac2types.rewriting
  type evar_flag = Tac2types.evars_flag
  type advanced_flag = Tac2types.advanced_flag
  type move_location = Id.t Logic.move_location
  type inversion_kind = Inv.inversion_kind

  val intros :
    evar_flag ->
    intro_pattern list ->
    unit Proofview.tactic

  val apply :
    advanced_flag ->
    evar_flag ->
    (unit -> constr_with_bindings Proofview.tactic) list ->
    (Id.t * intro_pattern option) option ->
    unit Proofview.tactic

  val elim :
    evar_flag ->
    constr_with_bindings ->
    constr_with_bindings option ->
    unit Proofview.tactic

  val case :
    evar_flag ->
    constr_with_bindings ->
    unit Proofview.tactic

  val generalize :
    (EConstr.constr * occurrences * Name.t)
    list ->
    unit Proofview.tactic

  val assert_ : assertion -> unit Proofview.tactic

  val enough :
    EConstr.constr ->
    (unit -> unit Proofview.tactic) option option ->
    intro_pattern option ->
    unit Proofview.tactic

  val pose :
    Name.t -> EConstr.constr -> unit Proofview.tactic

  val set :
    evar_flag ->
    (unit -> (Name.t * EConstr.constr) Proofview.tactic) ->
    clause ->
    unit Proofview.tactic

  val remember :
    evar_flag ->
    Name.t ->
    (unit -> EConstr.constr Proofview.tactic) ->
    intro_pattern option ->
    clause ->
    unit Proofview.tactic

  val destruct :
    evar_flag ->
    induction_clause list ->
    constr_with_bindings option ->
    unit Proofview.tactic

  val induction :
    evar_flag ->
    induction_clause list ->
    constr_with_bindings option ->
    unit Proofview.tactic

  val exfalso : unit -> unit Proofview.tactic

  module Red : sig
    type t = Redexpr.red_expr

    val red : t
    val hnf : t

    val simpl :
      red_flags ->
      Tac2types.red_context ->
      t Proofview.tactic

    val cbv : red_flags -> t Proofview.tactic
    val cbn : red_flags -> t Proofview.tactic
    val lazy_ : red_flags -> t Proofview.tactic

    val unfold :
      (reference * occurrences) list ->
      t Proofview.tactic

    val fold : EConstr.constr list -> t

    val pattern : (EConstr.constr * occurrences) list -> t

    val vm : Tac2types.red_context -> t
    val native : Tac2types.red_context -> t
  end

  val eval_in :
    Red.t ->
    clause ->
    unit Proofview.tactic

  val eval :
    Red.t ->
    EConstr.constr ->
    EConstr.constr Proofview.tactic

  val change :
    Pattern.constr_pattern option ->
    (EConstr.constr array, EConstr.constr) fun1 ->
    clause ->
    unit Proofview.tactic

  val rewrite :
    evar_flag ->
    rewriting list ->
    clause ->
    (unit -> unit Proofview.tactic) option ->
    unit Proofview.tactic

  val setoid_rewrite :
    orientation ->
    constr_with_bindings Proofview.tactic ->
    occurrences ->
    Id.t option ->
    unit Proofview.tactic

  val reflexivity : unit -> unit Proofview.tactic

  val assumption : unit -> unit Proofview.tactic
  val eassumption : unit -> unit Proofview.tactic
  val transitivity : EConstr.constr -> unit Proofview.tactic
  val etransitivity : unit -> unit Proofview.tactic
  val cut : EConstr.constr -> unit Proofview.tactic

  val left :
    evar_flag -> bindings -> unit Proofview.tactic

  val right :
    evar_flag -> bindings -> unit Proofview.tactic

  val constructor : evar_flag -> unit Proofview.tactic

  val split :
    evar_flag -> bindings -> unit Proofview.tactic

  val constructor_n :
    evar_flag -> int -> bindings -> unit Proofview.tactic

  val intros_until :
    hypothesis -> unit Proofview.tactic

  val symmetry : clause -> unit Proofview.tactic

  val rename :
    (Id.t * Id.t) list -> unit Proofview.tactic

  val revert : Id.t list -> unit Proofview.tactic

  val admit : unit -> unit Proofview.tactic

  val fix : Id.t -> int -> unit Proofview.tactic
  val cofix : Id.t -> unit Proofview.tactic

  val clear : Id.t list -> unit Proofview.tactic
  val keep : Id.t list -> unit Proofview.tactic

  val clearbody : Id.t list -> unit Proofview.tactic

  val exact_no_check :
    EConstr.constr -> unit Proofview.tactic
  val vm_cast_no_check :
    EConstr.constr -> unit Proofview.tactic
  val native_cast_no_check :
    EConstr.constr -> unit Proofview.tactic

  val inversion :
    Inv.inversion_kind ->
    destruction_arg ->
    intro_pattern option ->
    Id.t list option ->
    unit Proofview.tactic

  val move :
    Id.t ->
    move_location ->
    unit Proofview.tactic

  val intro :
    Id.t option ->
    move_location option ->
    unit Proofview.tactic

  val specialize :
    constr_with_bindings ->
    intro_pattern option ->
    unit Proofview.tactic

  val discriminate :
    evar_flag ->
    destruction_arg option ->
    unit Proofview.tactic

  val injection :
    evar_flag ->
    intro_pattern list option ->
    destruction_arg option ->
    unit Proofview.tactic

  val absurd : EConstr.constr -> unit Proofview.tactic
  val contradiction :
    constr_with_bindings option ->
    unit Proofview.tactic

  val autorewrite :
    bool ->
    (unit -> unit Proofview.tactic) option ->
    Id.t list ->
    clause ->
    unit Proofview.tactic

  val subst : Id.t list -> unit Proofview.tactic
  val subst_all : unit -> unit Proofview.tactic

  type debug = Hints.debug
  type strategy = Class_tactics.search_strategy

  val trivial :
    debug ->
    reference list ->
    Id.t list option ->
    unit Proofview.tactic

  val auto :
    debug ->
    int option ->
    reference list ->
    Id.t list option ->
    unit Proofview.tactic

  val eauto :
    debug ->
    int option ->
    reference list ->
    Id.t list option ->
    unit Proofview.tactic

  val typeclasses_eauto :
    strategy option ->
    int option ->
    Id.t list option ->
    unit Proofview.tactic

  val resolve_tc : EConstr.constr -> unit Proofview.tactic

  val unify :
    EConstr.constr -> EConstr.constr -> unit Proofview.tactic

  val congruence :
    int option ->
    EConstr.constr list option ->
    unit Proofview.tactic

  val simple_congruence :
    int option ->
    EConstr.constr list option ->
    unit Proofview.tactic

  val f_equal : unit Proofview.tactic
end

val intro_pattern : Tac2types.intro_pattern Tac2ffi.repr
