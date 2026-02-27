(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Generic arguments based on Ltac. *)

open Genarg
open Geninterp
open Tacexpr
open Names

let make0 ?dyn name =
  let wit = Genarg.make0 name in
  let () = Geninterp.register_val0 wit dyn in
  wit

let wit_intropattern = make0 "intropattern" (* To keep after deprecation phase but it will get a different parsing semantics (Tactic Notation and TACTIC EXTEND) in pltac.ml *)
let wit_simple_intropattern = make0 ~dyn:(val_tag (topwit wit_intropattern)) "simple_intropattern"
let wit_quant_hyp = make0 "quant_hyp"
let wit_constr_with_bindings = make0 "constr_with_bindings"
let wit_open_constr_with_bindings = make0 "open_constr_with_bindings"
let wit_bindings = make0 "bindings"
let wit_quantified_hypothesis = wit_quant_hyp


(** Abstract application, to print ltac functions *)
type appl =
  | UnnamedAppl (** For generic applications: nothing is printed *)
  | GlbAppl of (Names.KerName.t * Geninterp.Val.t list) list
       (** For calls to global constants, some may alias other. *)

type tacvalue =
  | VFun of appl * ltac_trace * Loc.t option * Geninterp.Val.t Id.Map.t *
      Name.t list * glob_tactic_expr
  | VRec of Geninterp.Val.t Id.Map.t ref * glob_tactic_expr

let wit_tactic : (raw_tactic_expr, glob_tactic_expr, tacvalue) genarg_type =
  make0 "tactic"

let wit_ltac_in_term = GenConstr.create "ltac_in_term"

let wit_ltac = Gentactic.make "ltac"

let wit_destruction_arg =
  make0 "destruction_arg"
