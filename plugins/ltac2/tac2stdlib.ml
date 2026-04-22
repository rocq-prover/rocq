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
open Genredexpr
open Tac2val
open Tac2ffi
open Tac2types
open Tac2extffi
open Tac2externals
open Tac2helpers
open Proofview.Notations

module Value = Tac2ffi

let to_name c = match Value.to_option Value.to_ident c with
| None -> Anonymous
| Some id -> Name id

let name = make_to_repr to_name

let to_occurrences = function
| ValInt 0 -> AllOccurrences
| ValBlk (0, [| vl |]) -> AllOccurrencesBut (Value.to_list Value.to_int vl)
| ValInt 1 -> NoOccurrences
| ValBlk (1, [| vl |]) -> OnlyOccurrences (Value.to_list Value.to_int vl)
| _ -> assert false

let occurrences = make_to_repr to_occurrences

let to_hyp_location_flag v = match Value.to_int v with
| 0 -> InHyp
| 1 -> InHypTypeOnly
| 2 -> InHypValueOnly
| _ -> assert false

let to_clause v = match Value.to_tuple v with
| [| hyps; concl |] ->
  let cast v = match Value.to_tuple v with
  | [| hyp; occ; flag |] ->
    (Value.to_ident hyp, to_occurrences occ, to_hyp_location_flag flag)
  | _ -> assert false
  in
  let hyps = Value.to_option (fun h -> Value.to_list cast h) hyps in
  { onhyps = hyps; concl_occs = to_occurrences concl; }
| _ -> assert false

let clause = make_to_repr to_clause

let to_red_strength = function
  | ValInt 0 -> Norm
  | ValInt 1 -> Head
  | _ -> assert false

let to_red_flag v : Tac2types.red_flag = match Value.to_tuple v with
| [| strength; beta; iota; fix; cofix; zeta; delta; const |] ->
  {
    rStrength = to_red_strength strength;
    rBeta = Value.to_bool beta;
    rMatch = Value.to_bool iota;
    rFix = Value.to_bool fix;
    rCofix = Value.to_bool cofix;
    rZeta = Value.to_bool zeta;
    rDelta = Value.to_bool delta;
    rConst = Value.to_list Value.to_reference const;
  }
| _ -> assert false

let red_flags = make_to_repr to_red_flag

let constr_with_occs = pair constr occurrences

let reference_with_occs = pair reference occurrences

let to_red_context = to_option (to_pair to_pattern to_occurrences)

let red_context = make_to_repr to_red_context

let rec to_intro_pattern v = match Value.to_block v with
| (0, [| b |]) -> IntroForthcoming (Value.to_bool b)
| (1, [| pat |]) -> IntroNaming (to_intro_pattern_naming pat)
| (2, [| act |]) -> IntroAction (to_intro_pattern_action act)
| _ -> assert false

and to_intro_pattern_naming = function
| ValBlk (0, [| id |]) -> IntroIdentifier (Value.to_ident id)
| ValBlk (1, [| id |]) -> IntroFresh (Value.to_ident id)
| ValInt 0 -> IntroAnonymous
| _ -> assert false

and to_intro_pattern_action = function
| ValInt 0 -> IntroWildcard
| ValBlk (0, [| op |]) -> IntroOrAndPattern (to_or_and_intro_pattern op)
| ValBlk (1, [| inj |]) ->
  let map ipat = to_intro_pattern ipat in
  IntroInjection (Value.to_list map inj)
| ValBlk (2, [| c; ipat |]) ->
  let c = Value.to_fun1 Value.of_unit Value.to_constr c in
  IntroApplyOn (c, to_intro_pattern ipat)
| ValBlk (3, [| b |]) -> IntroRewrite (Value.to_bool b)
| _ -> assert false

and to_or_and_intro_pattern v = match Value.to_block v with
| (0, [| ill |]) ->
  IntroOrPattern (Value.to_list to_intro_patterns ill)
| (1, [| il |]) ->
  IntroAndPattern (to_intro_patterns il)
| _ -> assert false

and to_intro_patterns il =
  Value.to_list to_intro_pattern il

let rec of_intro_pattern = function
  | IntroForthcoming b -> of_block (0, [|of_bool b|])
  | IntroNaming pat -> of_block (1, [|of_intro_pattern_naming pat|])
  | IntroAction act -> of_block (2, [|of_intro_pattern_action act|])

and of_intro_pattern_naming = function
  | IntroIdentifier id -> of_block (0, [|of_ident id|])
  | IntroFresh id -> of_block (1, [|of_ident id|])
  | IntroAnonymous -> of_int 0

and of_intro_pattern_action = function
  | IntroWildcard -> of_int 0
  | IntroOrAndPattern op -> of_block (0, [|of_or_and_intro_pattern op|])
  | IntroInjection inj -> of_block (1, [|of_list of_intro_pattern inj|])
  | IntroApplyOn (c, ipat) ->
    let c = repr_of (fun1 unit constr) c in
    of_block (2, [|c; of_intro_pattern ipat|])
  | IntroRewrite b -> of_block (3, [|of_bool b|])

and of_or_and_intro_pattern = function
  | IntroOrPattern ill -> of_block (0, [|of_list of_intro_patterns ill|])
  | IntroAndPattern il -> of_block (1, [|of_intro_patterns il|])

and of_intro_patterns il = of_list of_intro_pattern il

let intro_pattern = make_repr of_intro_pattern to_intro_pattern

let intro_patterns = make_repr of_intro_patterns to_intro_patterns

let to_destruction_arg v = match Value.to_block v with
| (0, [| c |]) ->
  let c = uthaw constr_with_bindings c in
  ElimOnConstr c
| (1, [| id |]) -> ElimOnIdent (Value.to_ident id)
| (2, [| n |]) -> ElimOnAnonHyp (Value.to_int n)
| _ -> assert false

let destruction_arg = make_to_repr to_destruction_arg

let to_induction_clause v = match Value.to_tuple v with
| [| arg; eqn; as_; in_ |] ->
  let arg = to_destruction_arg arg in
  let eqn = Value.to_option to_intro_pattern_naming eqn in
  let as_ = Value.to_option to_or_and_intro_pattern as_ in
  let in_ = Value.to_option to_clause in_ in
  (arg, eqn, as_, in_)
| _ ->
  assert false

let induction_clause = make_to_repr to_induction_clause

let to_assertion v = match Value.to_block v with
| (0, [| ipat; t; tac |]) ->
  let to_tac t = Value.to_fun1 Value.of_unit Value.to_unit t in
  let ipat = Value.to_option to_intro_pattern ipat in
  let t = Value.to_constr t in
  let tac = Value.to_option to_tac tac in
  AssertType (ipat, t, tac)
| (1, [| id; c |]) ->
  AssertValue (Value.to_ident id, Value.to_constr c)
| _ -> assert false

let assertion = make_to_repr to_assertion

let to_multi = function
| ValBlk (0, [| n |]) -> Precisely (Value.to_int n)
| ValBlk (1, [| n |]) -> UpTo (Value.to_int n)
| ValInt 0 -> RepeatStar
| ValInt 1 -> RepeatPlus
| _ -> assert false

let to_rewriting v = match Value.to_tuple v with
| [| orient; repeat; c |] ->
  let orient = Value.to_option Value.to_bool orient in
  let repeat = to_multi repeat in
  let c = uthaw constr_with_bindings c in
  (orient, repeat, c)
| _ -> assert false

let rewriting = make_to_repr to_rewriting

let to_debug v = match Value.to_int v with
| 0 -> Hints.Off
| 1 -> Hints.Info
| 2 -> Hints.Debug
| _ -> assert false

let debug = make_to_repr to_debug

let to_strategy v = match Value.to_int v with
| 0 -> Class_tactics.Bfs
| 1 -> Class_tactics.Dfs
| _ -> assert false

let strategy = make_to_repr to_strategy

let to_inversion_kind v = match Value.to_int v with
| 0 -> Inv.SimpleInversion
| 1 -> Inv.FullInversion
| 2 -> Inv.FullInversionClear
| _ -> assert false

let inversion_kind = make_to_repr to_inversion_kind


let to_move_location = function
| ValInt 0 -> Logic.MoveFirst
| ValInt 1 -> Logic.MoveLast
| ValBlk (0, [|id|]) -> Logic.MoveAfter (Value.to_ident id)
| ValBlk (1, [|id|]) -> Logic.MoveBefore (Value.to_ident id)
| _ -> assert false

let move_location = make_to_repr to_move_location

let to_generalize_arg v = match Value.to_tuple v with
| [| c; occs; na |] ->
  (Value.to_constr c, to_occurrences occs, to_name na)
| _ -> assert false

let generalize_arg = make_to_repr to_generalize_arg

(** Standard tactics sharing their implementation with Ltac1 *)

module Ltac2Std = struct
  (** ML-facing types *)
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

  let intros = Tac2tactics.intros_patterns

  let apply = Tac2tactics.apply

  let elim = Tac2tactics.elim
  let case = Tac2tactics.general_case_analysis

  let generalize = Tac2tactics.generalize

  let assert_ = Tac2tactics.assert_
  let enough c tac ipat =
    let tac = Option.map (fun o -> Option.map (fun f -> thaw f) o) tac in
    Tac2tactics.forward false tac ipat c

  let pose na c = Tactics.letin_tac None na c None Locusops.nowhere

  let set ev p cl =
    Proofview.tclEVARMAP >>= fun sigma ->
    thaw p >>= fun (na, c) ->
    Tac2tactics.letin_pat_tac ev None na (Some sigma, c) cl

  let remember ev na c eqpat cl =
    let eqpat = Option.default (IntroNaming IntroAnonymous) eqpat in
    match eqpat with
    | IntroNaming eqpat ->
       Proofview.tclEVARMAP >>= fun sigma ->
       thaw c >>= fun c ->
       Tac2tactics.letin_pat_tac ev (Some (true, eqpat)) na (Some sigma, c) cl
    | _ ->
       Tacticals.tclZEROMSG (Pp.str "Invalid pattern for remember")

  let destruct = Tac2tactics.induction_destruct false
  let induction = Tac2tactics.induction_destruct true

  let exfalso () = Tactics.exfalso

  module Red = struct
    type t = Redexpr.red_expr

    let red = Red
    let hnf = Hnf
    let simpl = Tac2tactics.simpl
    let cbv = Tac2tactics.cbv
    let cbn = Tac2tactics.cbn
    let lazy_ = Tac2tactics.lazy_
    let unfold = Tac2tactics.unfold
    let fold cs = Fold cs
    let pattern = Tac2tactics.pattern

    let vm = Tac2tactics.vm
    let native = Tac2tactics.native
  end

  let eval_in = Tac2tactics.reduce_in
  let eval = Tac2tactics.reduce_constr

  let change = Tac2tactics.change
  let rewrite = Tac2tactics.rewrite
  let setoid_rewrite = Tac2tactics.setoid_rewrite

  let inversion = Tac2tactics.inversion

  let reflexivity () = Tactics.intros_reflexivity

  let move = Tactics.move_hyp

  let intro id mv =
    let mv = Option.default Logic.MoveLast mv in
    Tactics.intro_move id mv

  let specialize = Tac2tactics.specialize

  let assumption () = Tactics.assumption
  let eassumption () = Eauto.e_assumption

  let transitivity c = Tactics.intros_transitivity (Some c)
  let etransitivity () = Tactics.intros_transitivity None

  let cut = Tactics.cut

  let left = Tac2tactics.left_with_bindings
  let right = Tac2tactics.right_with_bindings

  let intros_until = Tactics.intros_until

  let exact_no_check = Tactics.exact_no_check
  let vm_cast_no_check = Tactics.vm_cast_no_check
  let native_cast_no_check = Tactics.native_cast_no_check

  let constructor ev = Tactics.any_constructor ev None
  let constructor_n ev n bnd = Tac2tactics.constructor_tac ev None n bnd

  let symmetry = Tac2tactics.symmetry

  let split = Tac2tactics.split_with_bindings
  let rename = Tactics.rename_hyp

  let revert = Generalize.revert
  let admit () = Proofview.give_up

  let fix = FixTactics.fix
  let cofix = FixTactics.cofix

  let clear = Tactics.clear
  let keep = Tactics.keep
  let clearbody = Tactics.clear_body

  let discriminate = Tac2tactics.discriminate
  let injection = Tac2tactics.injection

  let absurd = Contradiction.absurd
  let contradiction = Tac2tactics.contradiction

  let autorewrite all by ids cl = Tac2tactics.autorewrite ~all by ids cl

  let subst = Equality.subst
  let subst_all () = return () >>= fun () -> Equality.subst_all ()

  type debug = Hints.debug
  type strategy = Class_tactics.search_strategy

  let trivial = Tac2tactics.trivial
  let auto = Tac2tactics.auto
  let eauto = Tac2tactics.eauto
  let typeclasses_eauto = Tac2tactics.typeclasses_eauto

  let resolve_tc = Class_tactics.resolve_tc

  let unify = Tac2tactics.unify

  let congruence = Tac2tactics.congruence
  let simple_congruence = Tac2tactics.simple_congruence

  let f_equal = Tac2tactics.f_equal
end

(** Tactics from Tacexpr *)

let () =
  define "tac_intros"
    (bool @-> intro_patterns @-> tac unit)
    Ltac2Std.intros

let () =
  define "tac_apply"
    (bool @-> bool @-> list (thunk constr_with_bindings) @->
      option (pair ident (option intro_pattern)) @-> tac unit)
    Ltac2Std.apply

let () =
  define "tac_elim"
    (bool @-> constr_with_bindings @-> option constr_with_bindings @-> tac unit)
    Ltac2Std.elim

let () =
  define "tac_case"
    (bool @-> constr_with_bindings @-> tac unit)
    Ltac2Std.case

let () =
  define "tac_generalize"
    (list generalize_arg @-> tac unit)
    Ltac2Std.generalize

let () =
  define "tac_assert"
    (assertion @-> tac unit)
    Ltac2Std.assert_

let () =
  define "tac_enough"
    (constr @-> option (option (thunk unit)) @-> option intro_pattern @-> tac unit)
    Ltac2Std.enough

let () =
  define "tac_pose"
    (name @-> constr @-> tac unit)
    Ltac2Std.pose

let () =
  define "tac_set"
    (bool @-> thunk (pair name constr) @-> clause @-> tac unit)
    Ltac2Std.set

let () =
  define "tac_remember"
    (bool @-> name @-> thunk constr @-> option intro_pattern @-> clause @-> tac unit)
    Ltac2Std.remember

let () =
  define "tac_destruct"
    (bool @-> list induction_clause @-> option constr_with_bindings @-> tac unit)
    Ltac2Std.destruct

let () =
  define "tac_induction"
    (bool @-> list induction_clause @-> option constr_with_bindings @-> tac unit)
    Ltac2Std.induction

let () = define "tac_exfalso" (unit @-> tac unit)
    Ltac2Std.exfalso

(** Reductions *)

let () =
  define "reduce_in"
    (reduction @-> clause @-> tac unit)
    Ltac2Std.eval_in

let () =
  define "reduce_constr"
    (reduction @-> constr @-> tac constr)
    Ltac2Std.eval

let () = define "red"
           (ret reduction)
           Ltac2Std.Red.red

let () = define "hnf" (ret reduction)
           Ltac2Std.Red.hnf

let () =
  define "simpl"
    (red_flags @-> red_context @-> tac reduction)
    Ltac2Std.Red.simpl

let () =
  define "cbv"
    (red_flags @-> tac reduction)
    Ltac2Std.Red.cbv

let () =
  define "cbn"
    (red_flags @-> tac reduction)
    Ltac2Std.Red.cbn

let () =
  define "lazy"
    (red_flags @-> tac reduction)
    Ltac2Std.Red.lazy_

let () =
  define "unfold"
    (list reference_with_occs @-> tac reduction)
    Ltac2Std.Red.unfold

let () =
  define "fold"
    (list constr @-> ret reduction)
    Ltac2Std.Red.fold

let () =
  define "pattern"
    (list constr_with_occs @-> ret reduction)
    Ltac2Std.Red.pattern

let () =
  define "vm"
    (red_context @-> ret reduction)
    Ltac2Std.Red.vm

let () =
  define "native"
    (red_context @-> ret reduction)
    Ltac2Std.Red.native


(** Rewritings *)

let () =
  define "tac_change"
    (option pattern @-> fun1 (array constr) constr @-> clause @-> tac unit)
    Ltac2Std.change

let () =
  define "tac_rewrite"
    (bool @-> list rewriting @-> clause @-> option (thunk unit) @-> tac unit)
    Ltac2Std.rewrite

let () =
  define "tac_setoid_rewrite"
    (bool @-> uthaw constr_with_bindings @--> occurrences @-> option ident @-> tac unit)
    Ltac2Std.setoid_rewrite

let () =
  define "tac_inversion"
    (inversion_kind @-> destruction_arg @-> option intro_pattern @->
      option (list ident) @-> tac unit)
    Ltac2Std.inversion

(** Tactics from coretactics *)

let () =
  define "tac_reflexivity" (unit @-> tac unit) Ltac2Std.reflexivity

let () =
  define "tac_move" (ident @-> move_location @-> tac unit) Ltac2Std.move

let () =
  define "tac_intro" (option ident @-> option move_location @-> tac unit) Ltac2Std.intro

(*

TACTIC EXTEND exact
  [ "exact" casted_constr(c) ] -> [ Tactics.exact_no_check c ]
END

*)

let () =
  define "tac_assumption" (unit @-> tac unit) Ltac2Std.assumption

let () =
  define "tac_eassumption" (unit @-> tac unit) Ltac2Std.eassumption

let () =
  define "tac_transitivity" (constr @-> tac unit) Ltac2Std.transitivity

let () =
  define "tac_etransitivity" (unit @-> tac unit) Ltac2Std.etransitivity

let () =
  define "tac_cut" (constr @-> tac unit) Ltac2Std.cut

let () =
  define "tac_left" (bool @-> bindings @-> tac unit) Ltac2Std.left

let () =
  define "tac_right" (bool @-> bindings @-> tac unit) Ltac2Std.right

let () =
  define "tac_introsuntil" (qhyp @-> tac unit) Ltac2Std.intros_until

let () =
  define "tac_exactnocheck" (constr @-> tac unit) Ltac2Std.exact_no_check

let () =
  define "tac_vmcastnocheck" (constr @-> tac unit) Ltac2Std.vm_cast_no_check

let () =
  define "tac_nativecastnocheck" (constr @-> tac unit) Ltac2Std.native_cast_no_check

let () =
  define "tac_constructor" (bool @-> tac unit) Ltac2Std.constructor

let () =
  define "tac_constructorn" (bool @-> int @-> bindings @-> tac unit) Ltac2Std.constructor_n

let () =
  define "tac_specialize" (constr_with_bindings @-> option intro_pattern @-> tac unit) Ltac2Std.specialize

let () =
  define "tac_symmetry" (clause @-> tac unit) Ltac2Std.symmetry

let () =
  define "tac_split" (bool @-> bindings @-> tac unit) Ltac2Std.split

let () =
  define "tac_rename" (list (pair ident ident) @-> tac unit) Ltac2Std.rename

let () =
  define "tac_revert" (list ident @-> tac unit) Ltac2Std.revert

let () =
  define "tac_admit" (unit @-> tac unit) Ltac2Std.admit

let () =
  define "tac_fix" (ident @-> int @-> tac unit) Ltac2Std.fix

let () =
  define "tac_cofix" (ident @-> tac unit) Ltac2Std.cofix

let () =
  define "tac_clear" (list ident @-> tac unit) Ltac2Std.clear

let () =
  define "tac_keep" (list ident @-> tac unit) Ltac2Std.keep

let () =
  define "tac_clearbody" (list ident @-> tac unit) Ltac2Std.clearbody

(** Tactics from extratactics *)

let () =
  define "tac_discriminate"
    (bool @-> option destruction_arg @-> tac unit)
    Ltac2Std.discriminate

let () =
  define "tac_injection"
    (bool @-> option intro_patterns @-> option destruction_arg @-> tac unit)
    Ltac2Std.injection

let () =
  define "tac_absurd" (constr @-> tac unit) Ltac2Std.absurd

let () =
  define "tac_contradiction"
    (option constr_with_bindings @-> tac unit)
    Ltac2Std.contradiction

let () =
  define "tac_autorewrite"
    (bool @-> option (thunk unit) @-> list ident @-> clause @-> tac unit)
    Ltac2Std.autorewrite

let () =
  define "tac_subst" (list ident @-> tac unit) Ltac2Std.subst

let () =
  define "tac_substall"
    (unit @-> tac unit)
    Ltac2Std.subst_all

(** Auto *)

let () =
  define "tac_trivial"
    (debug @-> list reference @-> option (list ident) @-> tac unit)
    Ltac2Std.trivial

let () =
  define "tac_eauto"
    (debug @-> option int @-> list reference @-> option (list ident) @-> tac unit)
    Ltac2Std.eauto

let () =
  define "tac_auto"
    (debug @-> option int @-> list reference @-> option (list ident) @-> tac unit)
    Ltac2Std.auto

let () =
  define "tac_typeclasses_eauto"
    (option strategy @-> option int @-> option (list ident) @-> tac unit)
    Ltac2Std.typeclasses_eauto

let () =
  define "tac_resolve_tc" (constr @-> tac unit) Ltac2Std.resolve_tc

let () =
  define "tac_unify" (constr @-> constr @-> tac unit) Ltac2Std.unify

let () =
  define "congruence"
    (option int @-> option (list constr) @-> tac unit)
    Ltac2Std.congruence

let () =
  define "simple_congruence"
    (option int @-> option (list constr) @-> tac unit)
    Ltac2Std.simple_congruence

let () = define "f_equal" (unit @-> tac unit) @@ fun () ->
    Ltac2Std.f_equal
