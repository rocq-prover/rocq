(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open EConstr
open Environ
open Evd
open Redexpr
open Pattern
open Locus
open Ltac_pretype

(** Tactics which deal with reduction and conversion. *)


(** {6 Basic conversion tactics. } *)

(** [convert ?pb x y] checks that [x] and [y] are convertible (using all conversion rules)
    and fails otherwise.
    - [pb]: whether to use conversion ([CONV]) or cumulativity ([CUMUL]). Defaults to [CONV]. *)
val convert : ?pb:conv_pb -> constr -> constr -> unit Proofview.tactic

(** [convert_concl ~cast ~check new_concl kind] changes the conclusion to [new_concl],
    which should be convertible to the old conclusion.
    - [cast]: if [true] insert a cast in the proof term using [kind] as the cast kind.
    - [check]: if [true] we check for convertibility. *)
val convert_concl : cast:bool -> check:bool -> types -> cast_kind -> unit Proofview.tactic

(** [convert_hyp ~check ~reorder decl] changes the declaration of [x] to [decl],
    where [x] is the variable bound by [decl].
    - [check]: if [true] we check that [x] is in the context, that the new and old declarations of [x]
      are convertible (both the types and bodies need to be convertible), and that the new
      declaration of [x] has a body if and only if the old declaration of [x] has a body. *)
val convert_hyp : check:bool -> reorder:bool -> named_declaration -> unit Proofview.tactic


(** {6 Specialized reduction strategies. } *)

(** [red loc] reduces the hypothesis or conclusion [loc] using the [red] reduction strategy. *)
val red : goal_location -> unit Proofview.tactic

(** [hnf loc] reduces the hypothesis or conclusion [loc] to head normal form. *)
val hnf : goal_location -> unit Proofview.tactic

(** [simpl loc] reduces the hypothesis or conclusion [loc] using the [simpl] reduction strategy. *)
val simpl : goal_location -> unit Proofview.tactic

(** [normalise loc] reduces the hypothesis or conclusion [loc] to normal form. *)
val normalise : goal_location -> unit Proofview.tactic

(** [normalise_vm_in_concl] reduces the conclusion to normal form using VM compute. *)
val normalise_vm_in_concl : unit Proofview.tactic

(** [unfold cs loc] unfolds a list of constants [cs] in the hypothesis or conclusion [loc].
    One can specify which occurences of each constant to unfold. *)
val unfold : (occurrences * Evaluable.t) list -> goal_location -> unit Proofview.tactic

(** [pattern [(occs1, t1); (occs2, t2); ...] loc] implements the [pattern] user tactic.
    It performs beta-expansion for the terms [ti] at occurences [occsi], in the goal location
    [loc] (i.e. either in the goal or in a hypothesis). *)
val pattern : (occurrences * constr) list -> goal_location -> unit Proofview.tactic

(** High-level reduction tactic. *)
val reduce : red_expr -> clause -> unit Proofview.tactic


(** {6 Generic conversion tactics. } *)

type change_arg = patvar_map -> env -> evar_map -> (evar_map * constr) Tacred.change

(** [make_change_arg x] builds the change function which always returns [Changed x]. *)
val make_change_arg : constr -> change_arg

(** [change_in_concl ~check where change_fun] changes the conclusion (or subterms of the conclusion) using
    the change function [change_fun].
    - [check]: if [true] we check that the new conclusion is convertible to the old conclusion.
    - [where]: if [None] then the whole conclusion is changed.
      If [Some (occs, patt)] then only the subterms of the conclusion which match occurences [occs]
      and pattern [patt] are changed. *)
val change_in_concl : check:bool -> (occurrences * constr_pattern) option -> change_arg -> unit Proofview.tactic

(** [change_concl new_concl] replaces the conclusion with [new_concl].
    Fails if the new conclusion and old conclusion are not convertible. *)
val change_concl : constr -> unit Proofview.tactic

(** [change_in_hyp ~check where change_fun hyp] is analogous to [change_in_concl] but works
    on the hypothesis [hyp] instead of the conclusion. *)
val change_in_hyp : check:bool -> (occurrences * constr_pattern) option -> change_arg ->
                        hyp_location -> unit Proofview.tactic

(** [change ~check where change_fun clause] applies the change function [change_fun].
    - [check]: if [true] we check that the changed terms are convertible to the old terms.
    - [clause]: specifies where to apply the change function: to the conclusion and/or to a (subset of) hypotheses.
    - [where]: if [None] we change the complete conclusion/hypothesis.
      If [Some patt] we change subterms matching pattern [patt]. *)
val change :
  check:bool -> constr_pattern option -> change_arg -> clause -> unit Proofview.tactic


(** {6 Generic reduction tactics. } *)

type tactic_reduction = Reductionops.reduction_function
type e_tactic_reduction = Reductionops.e_reduction_function

(** [reduct_in_hyp ~check ~reorder red_fun hyp] applies the reduction function [red_fun] in hypothesis [hyp].
    - [check]: if [true] we check that the new hypothesis is convertible to the old hypothesis. *)
val reduct_in_hyp : check:bool -> reorder:bool -> tactic_reduction -> hyp_location -> unit Proofview.tactic

(** [reduct_in_concl ~cast ~check (red_fun, kind)] applies the reduction function [red_fun] to the conclusion.
    - [cast]: if [true] we insert a cast  in the proof term using [kind] as the cast kind.
    - [check]: if [true] we check that the new conclusion is convertible to the old conclusion. *)
val reduct_in_concl : cast:bool -> check:bool -> tactic_reduction * cast_kind -> unit Proofview.tactic

(** [reduct_option] combines the behaviour of [reduct_in_hyp] and [reduct_in_concl].
    If reducing in the conclusion it will insert a cast. *)
val reduct_option : check:bool -> tactic_reduction * cast_kind -> goal_location -> unit Proofview.tactic

(** Same as [reduct_in_concl] but the reduction function can update the evar map. *)
val e_reduct_in_concl : cast:bool -> check:bool -> e_tactic_reduction * cast_kind -> unit Proofview.tactic
