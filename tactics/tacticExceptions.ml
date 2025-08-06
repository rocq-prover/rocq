(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Util
open Names
open Environ
open EConstr
open Evd
open Tactypes

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

let clear_in_global_msg = function
  | None -> mt ()
  | Some ref -> str " implicitly in " ++ Printer.pr_global ref

let clear_dependency_msg env sigma id err inglobal =
  let ppidupper = function Some id -> Id.print id | None -> str "This variable" in
  let ppid = function Some id -> Id.print id | None -> str "this variable" in
  let pp = clear_in_global_msg inglobal in
  match err with
  | Evarutil.OccurHypInSimpleClause None ->
      ppidupper id ++ str " is used" ++ pp ++ str " in conclusion."
  | Evarutil.OccurHypInSimpleClause (Some id') ->
      ppidupper id ++ strbrk " is used" ++ pp ++ str " in hypothesis " ++ Id.print id' ++ str"."
  | Evarutil.EvarTypingBreak ev ->
      str "Cannot remove " ++ ppid id ++
      strbrk " without breaking the typing of " ++
      Printer.pr_leconstr_env env sigma (mkEvar ev) ++ str"."
  | Evarutil.NoCandidatesLeft ev ->
      str "Cannot remove " ++ ppid id ++ str " as it would leave the existential " ++
      Printer.pr_existential_key env sigma ev ++ str" without candidates."

let replacing_dependency_msg env sigma id err inglobal =
  let pp = clear_in_global_msg inglobal in
  match err with
  | Evarutil.OccurHypInSimpleClause None ->
      str "Cannot change " ++ Id.print id ++ str ", it is used" ++ pp ++ str " in conclusion."
  | Evarutil.OccurHypInSimpleClause (Some id') ->
      str "Cannot change " ++ Id.print id ++
      strbrk ", it is used" ++ pp ++ str " in hypothesis " ++ Id.print id' ++ str"."
  | Evarutil.EvarTypingBreak ev ->
      str "Cannot change " ++ Id.print id ++
      strbrk " without breaking the typing of " ++
      Printer.pr_leconstr_env env sigma (mkEvar ev) ++ str"."
  | Evarutil.NoCandidatesLeft ev ->
      str "Cannot change " ++ Id.print id ++ str " as it would leave the existential " ++
      Printer.pr_existential_key env sigma ev ++ str" without candidates."

let msg_quantified_hypothesis = function
  | NamedHyp id ->
      str "quantified hypothesis named " ++ Id.print id.CAst.v
  | AnonHyp n ->
      pr_nth n ++
      str " non dependent hypothesis"

let explain_unexpected_extra_pattern bound pat =
  let nb = Option.get bound in
  let s1,s2,s3 = match pat with
  | IntroNaming (IntroIdentifier _) ->
      "name", (String.plural nb " introduction pattern"), "no"
  | _ -> "introduction pattern", "", "none" in
  str "Unexpected " ++ str s1 ++ str " (" ++
  (if Int.equal nb 0 then (str s3 ++ str s2) else
   (str "at most " ++ int nb ++ str s2)) ++ spc () ++
  str (if Int.equal nb 1 then "was" else "were") ++
  strbrk " expected in the branch)."

(** Internal exception used by [tactic_interp_error_handler]. *)
exception Unhandled

(** Top-level exception handler (pretty-prints an exception). *)
let tactic_interp_error_handler = function
  | IntroAlreadyDeclared id ->
      Id.print id ++ str " is already declared."
  | ClearDependency (env,sigma,id,err,inglobal) ->
      clear_dependency_msg env sigma id err inglobal
  | ReplacingDependency (env,sigma,id,err,inglobal) ->
      replacing_dependency_msg env sigma id err inglobal
  | AlreadyUsed id ->
      Id.print id ++ str " is already used."
  | UsedTwice id ->
      Id.print id ++ str" is used twice."
  | VariableHasNoValue id ->
      Id.print id ++ str" is not a defined hypothesis."
  | ConvertIncompatibleTypes (env,sigma,t1,t2) ->
      str "The first term has type" ++ spc () ++
      quote (Termops.Internal.print_constr_env env sigma t1) ++ spc () ++
      strbrk "while the second term has incompatible type" ++ spc () ++
      quote (Termops.Internal.print_constr_env env sigma t2) ++ str "."
  | ConvertNotAType ->
      str "Not a type."
  | NotConvertible ->
      str "Not convertible."
  | NotUnfoldable ->
     str "Cannot unfold a non-constant."
  | NoQuantifiedHypothesis (id,red) ->
      str "No " ++ msg_quantified_hypothesis id ++
      strbrk " in current goal" ++
      (if red then strbrk " even after head-reduction" else mt ()) ++ str"."
  | CannotFindInstance id ->
      str "Cannot find an instance for " ++ Id.print id ++ str"."
  | NothingToRewrite id ->
      str "Nothing to rewrite in " ++ Id.print id ++ str"."
  | IllFormedEliminationType ->
      str "The type of elimination clause is not well-formed."
  | UnableToApplyLemma (env,sigma,thm,t) ->
      str "Unable to apply lemma of type" ++ brk(1,1) ++
      quote (Printer.pr_leconstr_env env sigma thm) ++ spc() ++
      str "on hypothesis of type" ++ brk(1,1) ++
      quote (Printer.pr_leconstr_env env sigma t) ++
      str "."
  | DependsOnBody (idl,ids,where) ->
     let idl = List.filter (fun id -> Id.Set.mem id ids) idl in
     let on_the_bodies = function
       | [] -> assert false
       | [id] -> str " depends on the body of " ++ Id.print id
       | l -> str " depends on the bodies of " ++ pr_sequence Id.print l
     in
     (match where with
     | None -> str "Conclusion" ++ on_the_bodies idl
     | Some id -> str "Hypothesis " ++ Id.print id ++ on_the_bodies idl)
  | NotRightNumberConstructors n ->
      str "Not an inductive goal with " ++ int n ++ str (String.plural n " constructor") ++ str "."
  | NotEnoughConstructors ->
      str "Not enough constructors."
  | ConstructorNumberedFromOne ->
      str "The constructors are numbered starting from 1."
  | NoConstructors ->
      str "The type has no constructors."
  | UnexpectedExtraPattern (bound,pat) ->
      explain_unexpected_extra_pattern bound pat
  | CannotFindInductiveArgument ->
      str "Cannot find inductive argument of elimination scheme."
  | OneIntroPatternExpected ->
      str "Introduction pattern for one hypothesis expected."
  | KeepAndClearModifierOnlyForHypotheses ->
      str "keep/clear modifiers apply only to hypothesis names."
  | FixpointOnNonInductiveType ->
      str "Cannot do a fixpoint on a non inductive type."
  | NotEnoughProducts ->
      str "Not enough products."
  | AllMethodsInCoinductiveType ->
      str "All methods must construct elements in coinductive types."
  | ReplacementIllTyped e ->
      str "Replacement would lead to an ill-typed term:" ++ spc () ++ CErrors.print e
  | NotEnoughPremises ->
      str "Applied theorem does not have enough premises."
  | NeedDependentProduct ->
      str "Needs a non-dependent product."
  | _ -> raise Unhandled

let wrap_unhandled f e =
  try Some (f e)
  with Unhandled -> None

(** Register the exception handler so that exceptions are nicely printed to the user. *)
let _ = CErrors.register_handler (wrap_unhandled tactic_interp_error_handler)
