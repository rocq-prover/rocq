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
open Tac2extffi
open Tac2api
open Tac2externals
open Tac2helpers

let constr_flags = Ltac2.Constr.Pretype.Flags.constr_flags

let open_constr_no_classes_flags =
  let open Pretyping in
  {
  use_coercions = true;
  use_typeclasses = Pretyping.NoUseTC;
  solve_unification_constraints = true;
  fail_evar = false;
  expand_evars = false;
  program_mode = false;
  poly = PolyFlags.default;
  undeclared_evars_rr = false;
  unconstrained_sorts = false;
  }

let preterm_flags =
  let open Pretyping in
  {
  use_coercions = true;
  use_typeclasses = Pretyping.NoUseTC;
  solve_unification_constraints = true;
  fail_evar = false;
  expand_evars = false;
  program_mode = false;
  poly = PolyFlags.default;
  undeclared_evars_rr = false;
  unconstrained_sorts = false;
  }

(** Helper functions *)

let throw = Tac2helpers.throw
let pf_apply = Tac2helpers.pf_apply
let wrap_exceptions = Tac2helpers.wrap_exceptions

(** Printing *)

let () = define "print" (pp @-> ret unit) Ltac2.Message.print

let () = define "message_empty" (ret pp) Ltac2.Message.empty

let () = define "message_of_int" (int @-> ret pp) Ltac2.Message.of_int

let () = define "message_of_string" (string @-> ret pp) Ltac2.Message.of_string

let () = define "message_to_string" (pp @-> ret string) Ltac2.Message.to_string

let () = define "message_of_constr" (constr @-> tac pp) Ltac2.Message.of_constr

let () = define "message_of_lconstr" (constr @-> tac pp) Ltac2.Message.of_lconstr

let () = define "message_of_preterm" (preterm @-> tac pp) Ltac2.Message.of_preterm

let () = define "message_of_lpreterm" (preterm @-> tac pp) Ltac2.Message.of_lpreterm

let () = define "message_of_ident" (ident @-> ret pp) Ltac2.Message.of_ident

let () = define "constant_print" (constant @-> ret pp) Ltac2.Constant.print

let () = define "projection_print" (projection @-> ret pp) Ltac2.Proj.print

let () = define "ind_print" (inductive @-> ret pp) Ltac2.Ind.print

let () = define "constructor_print" (constructor @-> ret pp) Ltac2.Constructor.print

let () = define "message_of_exn" (valexpr @-> eret pp) Ltac2.Message.of_exn

let () = define "message_concat" (pp @-> pp @-> ret pp) Ltac2.Message.concat

let () = define "message_force_new_line" (ret pp) Ltac2.Message.force_new_line

let () = define "message_break" (int @-> int @-> ret pp) Ltac2.Message.break

let () = define "message_space" (ret pp) Ltac2.Message.space

let () = define "message_hbox" (pp @-> ret pp) Ltac2.Message.hbox

let () = define "message_vbox" (int @-> pp @-> ret pp) Ltac2.Message.vbox

let () = define "message_hvbox" (int @-> pp @-> ret pp) Ltac2.Message.hvbox

let () = define "message_hovbox" (int @-> pp @-> ret pp) Ltac2.Message.hovbox

let () = define "format_stop" (ret format) Ltac2.Message.Format.stop

let () = define "format_string" (format @-> ret format) Ltac2.Message.Format.string

let () = define "format_int" (format @-> ret format) Ltac2.Message.Format.int

let () = define "format_constr" (format @-> ret format) Ltac2.Message.Format.constr

let () = define "format_ident" (format @-> ret format) Ltac2.Message.Format.ident

let () = define "format_literal" (string @-> format @-> ret format) Ltac2.Message.Format.literal

let () = define "format_alpha" (format @-> ret format) Ltac2.Message.Format.alpha

let () = define "format_alpha0" (format @-> ret format) Ltac2.Message.Format.alpha0

let () = define "format_message" (format @-> ret format) Ltac2.Message.Format.message

let () = define "format_kfprintf" (closure @-> format @-> tac valexpr) Ltac2.Message.Format.kfprintf

let () = define "format_ikfprintf" (closure @-> valexpr @-> format @-> tac valexpr) @@ Ltac2.Message.Format.ikfprintf

(** Array *)

let () = define "array_empty" (ret valexpr) Ltac2.Array.empty

let () =
  define "array_make" (int @-> valexpr @-> tac valexpr) Ltac2.Array.make

let () =
  define "array_length" (block @-> ret int) Ltac2.Array.length

let () =
  define "array_set" (block @-> int @-> valexpr @-> tac unit) Ltac2.Array.set

let () =
  define "array_get" (block @-> int @-> tac valexpr) Ltac2.Array.get

let () =
  define "array_blit" (block @-> int @-> block @-> int @-> int @-> tac unit) Ltac2.Array.lowlevel_blit

let () =
  define "array_fill" (block @-> int @-> int @-> valexpr @-> tac unit) Ltac2.Array.lowlevel_fill

let () =
  define "array_concat" (list block @-> ret valexpr) Ltac2.Array.concat

(** Ident *)

let () = define "ident_equal" (ident @-> ident @-> ret bool) Ltac2.Ident.equal

let () = define "ident_to_string" (ident @-> ret string) Ltac2.Ident.to_string

let () = define "ident_of_string" (string @-> ret (option ident)) Ltac2.Ident.of_string

(** Int *)

let () = define "int_equal" (int @-> int @-> ret bool) Ltac2.Int.equal

let () = define "int_neg" (int @-> ret int) Ltac2.Int.neg
let () = define "int_abs" (int @-> ret int) Ltac2.Int.abs

let () = define "int_compare" (int @-> int @-> ret int) Ltac2.Int.compare
let () = define "int_add" (int @-> int @-> ret int) Ltac2.Int.add
let () = define "int_sub" (int @-> int @-> ret int) Ltac2.Int.sub
let () = define "int_mul" (int @-> int @-> ret int) Ltac2.Int.mul

let () = define "int_div" (int @-> int @-> tac int) Ltac2.Int.div
let () = define "int_mod" (int @-> int @-> tac int) Ltac2.Int.(mod)

let () = define "int_asr" (int @-> int @-> ret int)  Ltac2.Int.(asr)
let () = define "int_lsl" (int @-> int @-> ret int)  Ltac2.Int.(lsl)
let () = define "int_lsr" (int @-> int @-> ret int)  Ltac2.Int.(lsr)
let () = define "int_land" (int @-> int @-> ret int) Ltac2.Int.(land)
let () = define "int_lor" (int @-> int @-> ret int)  Ltac2.Int.(lor)
let () = define "int_lxor" (int @-> int @-> ret int) Ltac2.Int.(lxor)
let () = define "int_lnot" (int @-> ret int) Ltac2.Int.(lnot)

(** Char *)

let () = define "char_of_int" (int @-> tac char) Ltac2.Char.of_int

let () = define "char_to_int" (char @-> ret int) Ltac2.Char.to_int

(** String *)

let () = define "string_make" (int @-> char @-> tac bytes) Ltac2.String.make

let () = define "string_length" (bytes @-> ret int) Ltac2.String.length

let () = define "string_set" (bytes @-> int @-> char @-> tac unit) Ltac2.String.set

let () = define "string_get" (bytes @-> int @-> tac char) Ltac2.String.get

let () = define "string_concat" (bytes @-> list bytes @-> ret bytes) Ltac2.String.concat

let () = define "string_app" (bytes @-> bytes @-> ret bytes) Ltac2.String.app

let () = define "string_sub" (bytes @-> int @-> int @-> tac bytes) Ltac2.String.sub

let () = define "string_equal" (bytes @-> bytes @-> ret bool) Ltac2.String.equal

let () = define "string_compare" (bytes @-> bytes @-> ret int) Ltac2.String.compare

(** Pstring *)

let () = define "pstring_max_length" (ret uint63) Ltac2.Pstring.max_length
let () = define "pstring_to_string" (pstring @-> ret string) Ltac2.Pstring.to_string
let () = define "pstring_of_string" (string @-> ret (option pstring)) Ltac2.Pstring.of_string
let () = define "pstring_make" (uint63 @-> uint63 @-> ret pstring) Ltac2.Pstring.make
let () = define "pstring_length" (pstring @-> ret uint63) Ltac2.Pstring.length
let () = define "pstring_get" (pstring @-> uint63 @-> ret uint63) Ltac2.Pstring.get
let () = define "pstring_sub" (pstring @-> uint63 @-> uint63 @-> ret pstring) Ltac2.Pstring.sub
let () = define "pstring_cat" (pstring @-> pstring @-> ret pstring) Ltac2.Pstring.cat
let () = define "pstring_equal" (pstring @-> pstring @-> ret bool) Ltac2.Pstring.equal
let () = define "pstring_compare" (pstring @-> pstring @-> ret int) Ltac2.Pstring.compare

(** Terms *)

(** constr -> constr *)
let () =
  define "constr_type" (constr @-> tac valexpr) Ltac2.Constr.type_

(** constr -> constr *)
let () =
  define "constr_equal" (constr @-> constr @-> tac bool) Ltac2.Constr.equal

let () =
  define "constr_kind" (constr @-> eret valexpr) Ltac2.Constr.Unsafe.kind

let () =
  define "constr_make" (valexpr @-> eret constr) Ltac2.Constr.Unsafe.make

let () =
  define "constr_check" (constr @-> tac valexpr) Ltac2.Constr.Unsafe.check

let () =
  define "constr_liftn" (int @-> int @-> constr @-> ret constr) Ltac2.Constr.Unsafe.liftn

let () =
  define "constr_substnl" (list constr @-> int @-> constr @-> ret constr) Ltac2.Constr.Unsafe.substnl

let () =
  define "constr_closenl" (list ident @-> int @-> constr @-> tac constr) Ltac2.Constr.Unsafe.closenl

let () =
  define "constr_closedn" (int @-> constr @-> tac bool) Ltac2.Constr.Unsafe.closednl

let () =
  define "constr_noccur_between" (int @-> int @-> constr @-> tac bool) Ltac2.Constr.Unsafe.noccur_between

let () =
  define "constr_case" (inductive @-> tac valexpr) Ltac2.Constr.Unsafe.case

let () =
  define "case_to_inductive" (case @-> ret inductive) Ltac2.Constr.Unsafe.Case.inductive

let () = define "constr_cast_default" (ret valexpr) Ltac2.Constr.Cast.default
let () = define "constr_cast_vm" (ret valexpr) Ltac2.Constr.Cast.vm
let () = define "constr_cast_native" (ret valexpr) Ltac2.Constr.Cast.native

let () =
  define "constr_in_context" (ident @-> constr @-> thunk unit @-> tac constr) Ltac2.Constr.in_context

(** preterm -> constr *)
let () = define "constr_flags" (ret pretype_flags) Ltac2.Constr.Pretype.Flags.constr_flags

let () =
  define "pretype_flags_set_use_coercions"
    (bool @-> pretype_flags @-> ret pretype_flags)
    Ltac2.Constr.Pretype.Flags.set_use_coercion

let () =
  define "pretype_flags_set_use_typeclasses"
    (bool @-> pretype_flags @-> ret pretype_flags)
    Ltac2.Constr.Pretype.Flags.set_use_typeclasses

let () =
  define "pretype_flags_set_allow_evars"
    (bool @-> pretype_flags @-> ret pretype_flags)
    Ltac2.Constr.Pretype.Flags.set_allow_evars

let () =
  define "pretype_flags_set_nf_evars"
    (bool @-> pretype_flags @-> ret pretype_flags)
    Ltac2.Constr.Pretype.Flags.set_nf_evars

let () = define "expected_istype" (ret expected_type) Ltac2.Constr.Pretype.expected_istype

let () = define "expected_oftype" (constr @-> ret expected_type) Ltac2.Constr.Pretype.expected_oftype

let () = define "expected_without_type_constraint" (ret expected_type)
           Ltac2.Constr.Pretype.expected_without_type_constraint

let () =
  define "constr_pretype" (pretype_flags @-> expected_type @-> preterm @-> tac constr) Ltac2.Constr.Pretype.pretype

let () =
  define "constr_binder_make" (option ident @-> constr @-> tac binder) Ltac2.Constr.Binder.make

let () =
  define "constr_binder_unsafe_make" (option ident @-> relevance @-> constr @-> ret binder) Ltac2.Constr.Binder.unsafe_make

let () =
  define "constr_binder_name" (binder @-> ret (option ident)) Ltac2.Constr.Binder.name

let () =
  define "constr_binder_type" (binder @-> ret constr) Ltac2.Constr.Binder.type_

let () =
  define "constr_binder_relevance" (binder @-> ret relevance) Ltac2.Constr.Binder.relevance

let () =
  define "constr_relevance_equal" (relevance @-> relevance @-> eret bool) Ltac2.Constr.Relevance.equal

let () = define "constr_relevance_relevant" (ret relevance) Ltac2.Constr.Relevance.relevant

let () = define "constr_relevance_irrelevant" (ret relevance) Ltac2.Constr.Relevance.irrelevant

let () =
  define "constr_has_evar" (constr @-> tac bool) Ltac2.Constr.has_evar

(** Uint63 *)

let () = define "uint63_compare" (uint63 @-> uint63 @-> ret int) Ltac2.Uint63.compare

let () = define "uint63_of_int" (int @-> ret uint63) Ltac2.Uint63.of_int

let () = define "uint63_print" (uint63 @-> ret pp) Ltac2.Uint63.print

(** Extra equalities *)

let () = define "evar_equal" (evar @-> evar @-> ret bool) Ltac2.Evar.equal
let () = define "float_equal" (float @-> float @-> ret bool) Ltac2.Float.equal
let () = define "uint63_equal" (uint63 @-> uint63 @-> ret bool) Ltac2.Uint63.equal
let () = define "meta_equal" (int @-> int @-> ret bool) Ltac2.Meta.equal
let () = define "constr_cast_equal" (cast @-> cast @-> ret bool) Ltac2.Constr.Cast.equal

let () =
  define "constant_equal" (constant @-> constant @-> ret bool) Ltac2.Constant.equal
let () =
  define "constr_case_equal" (case @-> case @-> ret bool) Ltac2.Constr.Unsafe.Case.equal
let () =
  define "constructor_equal" (constructor @-> constructor @-> ret bool) Ltac2.Constructor.equal
let () =
  define "projection_equal" (projection @-> projection @-> ret bool) Ltac2.Proj.equal


(** Patterns *)

let () =
  define "pattern_empty_context" (ret matching_context)
    Ltac2.Pattern.empty_context

let () =
  define "pattern_matches" (pattern @-> constr @-> tac valexpr)
    Ltac2.Pattern.matches

let () =
  define "pattern_matches_subterm" (pattern @-> constr @-> tac (pair matching_context (list (pair ident constr))))
    Ltac2.Pattern.matches_subterm

let () =
  define "pattern_matches_vect" (pattern @-> constr @-> tac valexpr)
    Ltac2.Pattern.matches_vect

let () =
  define "pattern_matches_subterm_vect" (pattern @-> constr @-> tac (pair matching_context (array constr)))
    Ltac2.Pattern.matches_subterm_vect


let match_pattern = Tac2ffi.map_repr
                      (fun (b,pat) -> if b then Tac2match.MatchPattern pat else Tac2match.MatchContext pat)
                      (function Tac2match.MatchPattern pat -> (true, pat) | MatchContext pat -> (false, pat))
                      (pair bool pattern)

let () =
  define "pattern_matches_goal"
    (bool @-> list (pair (option match_pattern) match_pattern) @-> match_pattern @-> tac valexpr)
    Ltac2.Pattern.matches_goal

let () =
  define "pattern_instantiate"
    (matching_context @-> constr @-> ret constr)
    Ltac2.Pattern.instantiate

(** Error *)

let () =
  define "throw" (exn @-> tac valexpr) Ltac2.Control.throw

let () =
  define "throw_bt" (exn @-> exninfo @-> tac valexpr) Ltac2.Control.throw_bt

let () =
  define "clear_err_info" (err @-> ret err) Ltac2.Control.clear_err_info

let () = define "current_exninfo" (unit @-> tac exninfo) Ltac2.Control.current_exninfo

let () = define "message_of_exninfo" (exninfo @-> ret pp) Ltac2.Message.of_exninfo

let () = define "print_err" (err @-> ret pp) Ltac2.Control.print_err

(** Control *)

(** exn -> 'a *)
let () =
  define "zero" (exn @-> tac valexpr) Ltac2.Control.zero

let () =
  define "zero_bt" (exn @-> exninfo @-> tac valexpr)
    Ltac2.Control.zero_bt

(** (unit -> 'a) -> (exn -> 'a) -> 'a *)
let () =
  define "plus" (thunk valexpr @-> fun1 exn valexpr @-> tac valexpr)
    Ltac2.Control.plus

let () =
  define "plus_bt" (thunk valexpr @-> fun2 exn exninfo valexpr @-> tac valexpr)
    Ltac2.Control.plus_bt

(** (unit -> 'a) -> 'a *)
let () =
  define "once" (thunk valexpr @-> tac valexpr)
    Ltac2.Control.once

(** (unit -> 'a) -> ('a * ('exn -> 'a)) result *)
let () =
  define "case" (thunk valexpr @-> tac (result (pair valexpr (fun1 exn valexpr))))
    Ltac2.Control.case

let () =
  define "numgoals" (unit @-> tac int)
    Ltac2.Control.numgoals

(** (unit -> unit) list -> unit *)
let () = define "dispatch" (list (thunk unit) @-> tac unit) Ltac2.Control.dispatch

(** (unit -> unit) list -> (unit -> unit) -> (unit -> unit) list -> unit *)
let () = define "extend" (list (thunk unit) @-> thunk unit @-> list (thunk unit) @-> tac unit) Ltac2.Control.extend

(** (unit -> unit) -> unit *)
let () = define "enter" (thunk unit @-> tac unit) Ltac2.Control.enter

(** int -> int -> (unit -> 'a) -> 'a *)
let () = define "focus" (int @-> int @-> thunk valexpr @-> tac valexpr) Ltac2.Control.focus

(** int -> unit **)
let () = define "cycle" (int @-> tac unit) Ltac2.Control.cycle

(** unit -> unit *)
let () = define "shelve" (unit @-> tac unit) Ltac2.Control.shelve

(** unit -> unit *)
let () =
  define "shelve_unifiable" (unit @-> tac unit)
    Ltac2.Control.shelve_unifiable

let () =
  define "new_goal" (evar @-> tac unit)
    Ltac2.Control.new_goal

let () =
  define "reorder_goals" (list int @-> tac unit)
    Ltac2.Control.reorder_goals

let () = define "unshelve" (thunk valexpr @-> tac valexpr) Ltac2.Control.unshelve

(** unit -> constr *)
let () = define "goal" (unit @-> tac constr) Ltac2.Control.goal

(** ident -> constr *)
let () = define "hyp" (ident @-> tac constr) Ltac2.Control.hyp

let () = define "hyp_value" (ident @-> tac (option constr)) Ltac2.Control.hyp_value

let () = define "hyps" (unit @-> tac valexpr) Ltac2.Control.hyps

(** (unit -> constr) -> unit *)
let () = define "refine" (thunk constr @-> tac unit) Ltac2.Control.refine

let () = define "solve_constraints" (unit @-> tac unit) Ltac2.Control.solve_constraints

let () = define "with_holes" (thunk valexpr @-> fun1 valexpr valexpr @-> tac valexpr) Ltac2.Control.with_holes

let () = define "progress" (thunk valexpr @-> tac valexpr) Ltac2.Control.progress

let () = define "abstract" (option ident @-> thunk unit @-> tac unit) Ltac2.Control.abstract

let () = define "time" (option string @-> thunk valexpr @-> tac valexpr) Ltac2.Control.time

let () = define "timeout" (int @-> thunk valexpr @-> tac valexpr) Ltac2.Control.timeout

let () = define "timeoutf" (float @-> thunk valexpr @-> tac valexpr) Ltac2.Control.timeoutf

let () = define "check_interrupt" (unit @-> tac unit) Ltac2.Control.check_interrupt

(** Fresh *)

let () = define "fresh_free_empty" (ret free) Ltac2.Fresh.Free.empty

let () = define "fresh_free_add" (ident @-> free @-> ret free) Ltac2.Fresh.Free.add

let () = define "fresh_free_union" (free @-> free @-> ret free) Ltac2.Fresh.Free.union

let () = define "fresh_free_of_ids" (list ident @-> ret free) Ltac2.Fresh.Free.of_ids

let () = define "fresh_free_of_constr" (constr @-> tac free) Ltac2.Fresh.Free.of_constr

let () = define "fresh_next" (free @-> ident @-> ret (pair ident free)) Ltac2.Fresh.next

let () = define "fresh_fresh" (free @-> ident @-> ret ident) Ltac2.Fresh.fresh

(** Env *)

let () = define "env_get" (list ident @-> ret (option reference)) Ltac2.Env.get

let () = define "env_expand" (list ident @-> ret (list reference)) Ltac2.Env.expand

let () = define "env_path" (reference @-> tac (list ident)) Ltac2.Env.path

let () = define "env_instantiate" (reference @-> tac constr) Ltac2.Env.instantiate

(** Ind *)

let () = define "ind_equal" (inductive @-> inductive @-> ret bool) Ltac2.Ind.equal

let () = define "ind_data" (inductive @-> tac ind_data) Ltac2.Ind.data

let () = define "ind_repr" (ind_data @-> ret inductive) Ltac2.Ind.repr
let () = define "ind_index" (inductive @-> ret int) Ltac2.Ind.index

let () = define "ind_nblocks" (ind_data @-> ret int) Ltac2.Ind.nblocks

let () = define "ind_nconstructors" (ind_data @-> ret int) Ltac2.Ind.nconstructors

let () = define "ind_get_block" (ind_data @-> int @-> tac ind_data) Ltac2.Ind.get_block

let () = define "ind_get_constructor" (ind_data @-> int @-> tac constructor) Ltac2.Ind.get_constructor

let () = define "ind_get_nparams" (ind_data @-> ret int) Ltac2.Ind.nparams

let () = define "ind_get_nparams_rec" (ind_data @-> ret int) Ltac2.Ind.nparams_uniform

let () = define "constructor_inductive" (constructor @-> ret inductive) Ltac2.Constructor.inductive

let () = define "constructor_index" (constructor @-> ret int) Ltac2.Constructor.index

let () = define "constructor_nargs" (ind_data @-> ret (array int)) Ltac2.Ind.constructor_nargs

let () = define "constructor_ndecls" (ind_data @-> ret (array int)) Ltac2.Ind.constructor_ndecls

let () = define "ind_get_projections" (ind_data @-> ret (option (array projection))) Ltac2.Ind.get_projections

(** Schemes *)

let () = define "scheme_lookup" (scheme_kind @-> reference @-> ret (option reference)) Ltac2.Scheme.lookup

let () = define "scheme_kind_rect_dep" (ret scheme_kind) Ltac2.Scheme.rect_dep
let () = define "scheme_kind_rec_dep" (ret scheme_kind) Ltac2.Scheme.rec_dep
let () = define "scheme_kind_ind_dep" (ret scheme_kind) Ltac2.Scheme.ind_dep
let () = define "scheme_kind_sind_dep" (ret scheme_kind) Ltac2.Scheme.sind_dep
let () = define "scheme_kind_rect_nodep" (ret scheme_kind) Ltac2.Scheme.rect_nodep
let () = define "scheme_kind_rec_nodep" (ret scheme_kind) Ltac2.Scheme.rec_nodep
let () = define "scheme_kind_ind_nodep" (ret scheme_kind) Ltac2.Scheme.ind_nodep
let () = define "scheme_kind_sind_nodep" (ret scheme_kind) Ltac2.Scheme.sind_nodep
let () = define "scheme_kind_case_dep" (ret scheme_kind) Ltac2.Scheme.case_dep
let () = define "scheme_kind_case_nodep" (ret scheme_kind) Ltac2.Scheme.case_nodep
let () = define "scheme_kind_casep_dep" (ret scheme_kind) Ltac2.Scheme.casep_dep
let () = define "scheme_kind_casep_nodep" (ret scheme_kind) Ltac2.Scheme.casep_nodep
let () = define "scheme_kind_scase_dep" (ret scheme_kind) Ltac2.Scheme.scase_dep
let () = define "scheme_kind_scase_nodep" (ret scheme_kind) Ltac2.Scheme.scase_nodep
let () = define "scheme_kind_sym" (ret scheme_kind) Ltac2.Scheme.sym
let () = define "scheme_kind_sym_involutive" (ret scheme_kind) Ltac2.Scheme.sym_involutive
let () = define "scheme_kind_rew" (ret scheme_kind) Ltac2.Scheme.rew
let () = define "scheme_kind_rew_dep" (ret scheme_kind) Ltac2.Scheme.rew_dep
let () = define "scheme_kind_rew_fwd_dep" (ret scheme_kind) Ltac2.Scheme.rew_fwd_dep
let () = define "scheme_kind_rew_r" (ret scheme_kind) Ltac2.Scheme.rew_r
let () = define "scheme_kind_rew_r_dep" (ret scheme_kind) Ltac2.Scheme.rew_r_dep
let () = define "scheme_kind_rew_fwd_r_dep" (ret scheme_kind) Ltac2.Scheme.rew_fwd_r_dep
let () = define "scheme_kind_congr" (ret scheme_kind) Ltac2.Scheme.congr
let () = define "scheme_kind_beq" (ret scheme_kind) Ltac2.Scheme.beq
let () = define "scheme_kind_dec_bl" (ret scheme_kind) Ltac2.Scheme.dec_bl
let () = define "scheme_kind_dec_lb" (ret scheme_kind) Ltac2.Scheme.dec_lb
let () = define "scheme_kind_eq_dec" (ret scheme_kind) Ltac2.Scheme.eq_dec

(** Proj *)

let () = define "projection_ind" (projection @-> ret inductive) Ltac2.Proj.ind

let () = define "projection_index" (projection @-> ret int) Ltac2.Proj.index

let () = define "projection_unfolded" (projection @-> ret bool) Ltac2.Proj.unfolded

let () = define "projection_set_unfolded" (projection @-> bool @-> ret projection) Ltac2.Proj.set_unfolded

let () = define "projection_of_constant" (constant @-> ret (option projection)) Ltac2.Proj.of_constant

let () = define "projection_to_constant" (projection @-> ret (option constant)) Ltac2.Proj.to_constant

let () = define "module_equal" (modpath @-> modpath @-> ret bool)
           Ltac2.Module.equal

let () = define "module_to_message" (modpath @-> ret pp)
           Ltac2.Module.to_message

let () = define "module_is_modtype" (modpath @-> eret bool)
           Ltac2.Module.is_modtype

let () = define "module_is_functor" (modpath @-> eret bool)
           Ltac2.Module.is_functor

let () = define "module_is_bound_module" (modpath @-> ret bool)
           Ltac2.Module.is_bound_module

let () = define "module_is_library" (modpath @-> ret bool)
           Ltac2.Module.is_library

let () = define "module_is_open" (modpath @-> ret bool) Ltac2.Module.is_open

let () = define "module_parent_module" (modpath @-> ret (option modpath))
           Ltac2.Module.parent_module

let () = define "module_of_reference" (reference @-> tac modpath)
           Ltac2.Module.module_of_reference

let () = define "current_module" (unit @-> ret modpath)
           Ltac2.Module.current_module

let () = define "module_loaded_libraries" (unit @-> ret (list modpath))
           Ltac2.Module.loaded_libraries

let module_field_handler = triple (fun1 modpath valexpr) (fun1 reference valexpr) (fun1 unit valexpr)

let () = define "module_field_handle" (module_field @-> module_field_handler @-> tac valexpr) Ltac2.Module.Field.handle

let () = define "module_contents" (modpath @-> ret (option (list module_field))) Ltac2.Module.contents

(** FMap/FSet *)

let () =
  define "fset_empty" (map_tag_repr @-> ret valexpr) Ltac2.FSet.empty

let () =
  define "fset_is_empty" (set_repr @-> ret bool) Ltac2.FSet.is_empty

let () =
  define "fset_mem" (valexpr @-> set_repr @-> ret bool) Ltac2.FSet.mem

let () =
  define "fset_add" (valexpr @-> set_repr @-> ret valexpr) Ltac2.FSet.add

let () =
  define "fset_remove" (valexpr @-> set_repr @-> ret valexpr) Ltac2.FSet.remove

let () =
  define "fset_union" (set_repr @-> set_repr @-> ret valexpr) Ltac2.FSet.union

let () =
  define "fset_inter" (set_repr @-> set_repr @-> ret valexpr) Ltac2.FSet.inter

let () =
  define "fset_diff" (set_repr @-> set_repr @-> ret valexpr) Ltac2.FSet.diff

let () =
  define "fset_equal" (set_repr @-> set_repr @-> ret bool) Ltac2.FSet.equal

let () =
  define "fset_subset" (set_repr @-> set_repr @-> ret bool) Ltac2.FSet.subset

let () =
  define "fset_cardinal" (set_repr @-> ret int) Ltac2.FSet.cardinal

let () =
  define "fset_elements" (set_repr @-> ret valexpr) Ltac2.FSet.elements

let () =
  define "fmap_empty" (map_tag_repr @-> ret valexpr) Ltac2.FMap.empty

let () =
  define "fmap_is_empty" (map_repr @-> ret bool) Ltac2.FMap.is_empty

let () =
  define "fmap_mem" (valexpr @-> map_repr @-> ret bool) Ltac2.FMap.mem

let () =
  define "fmap_add" (valexpr @-> valexpr @-> map_repr @-> ret valexpr) Ltac2.FMap.add

let () =
  define "fmap_remove" (valexpr @-> map_repr @-> ret valexpr) Ltac2.FMap.remove

let () =
  define "fmap_find_opt" (valexpr @-> map_repr @-> ret (option valexpr)) Ltac2.FMap.find_opt

let () =
  define "fmap_mapi" (closure @-> map_repr @-> tac valexpr) Ltac2.FMap.mapi

let () =
  define "fmap_fold" (closure @-> map_repr @-> valexpr @-> tac valexpr) Ltac2.FMap.fold

let () =
  define "fmap_cardinal" (map_repr @-> ret int) Ltac2.FMap.cardinal

let () =
  define "fmap_bindings" (map_repr @-> ret valexpr) Ltac2.FMap.bindings

let () =
  define "fmap_domain" (map_repr @-> ret valexpr) Ltac2.FMap.domain
