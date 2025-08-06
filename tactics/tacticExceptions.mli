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
open EConstr
open Environ
open Evd
open Tactypes

(** Common exceptions raised by tactics. These exceptions are catched at
    toplevel (the handler is defined in this file) and pretty-printed to the user. *)

exception IntroAlreadyDeclared of Id.t
exception ClearDependency of env * evar_map * Id.t option * Evarutil.clear_dependency_error * GlobRef.t option
exception ReplacingDependency of env * evar_map * Id.t * Evarutil.clear_dependency_error * GlobRef.t option
exception AlreadyUsed of Id.t
exception UsedTwice of Id.t
exception VariableHasNoValue of Id.t
exception ConvertIncompatibleTypes of env * evar_map * constr * constr
exception ConvertNotAType
exception NotConvertible
exception NotUnfoldable
exception NoQuantifiedHypothesis of quantified_hypothesis * bool
exception CannotFindInstance of Id.t
exception NothingToRewrite of Id.t
exception IllFormedEliminationType
exception UnableToApplyLemma of env * evar_map * constr * constr
exception DependsOnBody of Id.t list * Id.Set.t * Id.t option
exception NotRightNumberConstructors of int
exception NotEnoughConstructors
exception ConstructorNumberedFromOne
exception NoConstructors
exception UnexpectedExtraPattern of int option * delayed_open_constr intro_pattern_expr
exception CannotFindInductiveArgument
exception OneIntroPatternExpected
exception KeepAndClearModifierOnlyForHypotheses
exception FixpointOnNonInductiveType
exception NotEnoughProducts
exception AllMethodsInCoinductiveType
exception ReplacementIllTyped of exn
exception NotEnoughPremises
exception NeedDependentProduct

val clear_dependency_msg : env -> evar_map -> Names.Id.t option ->
    Evarutil.clear_dependency_error -> GlobRef.t option -> Pp.t
