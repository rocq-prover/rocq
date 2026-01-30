(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names

type raw_generic_tactic = Genarg.raw_generic_argument

type glob_generic_tactic = Genarg.glob_generic_argument

type ('raw, 'glob) tag = ('raw, 'glob, Empty.t) Genarg.genarg_type

let make name = Genarg.make0 name

let empty = make "empty"

let of_raw (type a) (tag:(a, _) tag) (x:a) : raw_generic_tactic =
  GenArg (Rawwit tag, x)

let to_raw_genarg x = x

let register_print = Genprint.register_noval_print0

let print_raw = Pputils.pr_raw_generic

let print_glob = Pputils.pr_glb_generic

let register_subst = Gensubst.register_subst0

let subst = Gensubst.generic_substitute

let register_intern = Genintern.register_intern0

let intern ?(strict=true) env ?(ltacvars=Id.Set.empty) v =
  let ist = { (Genintern.empty_glob_sign ~strict env) with ltacvars } in
  let _, v = Genintern.generic_intern ist v in
  v

type 'glb interp_fun = Geninterp.Val.t Id.Map.t -> 'glb -> unit Proofview.tactic

module InterpObj =
struct
  type ('raw, 'glb, 'top) obj = 'glb interp_fun
  let name = "gentactic.interp"
  let default _ = None
end

module Interp = Genarg.Register(InterpObj)

let register_interp = Interp.register0

let interp ?(lfun=Id.Map.empty) (Genarg.GenArg (Glbwit tag, v)) =
  let interp : _ interp_fun = Interp.obj tag in
  interp lfun v

let wit_generic_tactic = Genarg.make0 "generic_tactic"

let () =
  let mkprint f v = Genprint.PrinterBasic (fun env sigma -> f env sigma v) in
  Genprint.register_vernac_print0 wit_generic_tactic (mkprint (print_raw ?level:None));
