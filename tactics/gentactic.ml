(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

module TDyn = Dyn.Make()

type ('raw, 'glb) tag = ('raw * 'glb) TDyn.tag

type raw_generic_tactic = Raw : ('raw, _) tag * 'raw -> raw_generic_tactic

type glob_generic_tactic = Glb : (_, 'glb) tag * 'glb -> glob_generic_tactic

let make name : _ tag = TDyn.create name

let empty = make "empty"

let of_raw (type a) (tag:(a, _) tag) (x:a) : raw_generic_tactic =
  Raw (tag, x)

module Print = struct
  type _ t = Print : {
      raw_print : 'raw Genprint.printer;
      glb_print : 'glb Genprint.printer;
    } -> ('raw * 'glb) t
end

module PrintMap = TDyn.Map(Print)

let printers = ref PrintMap.empty

let register_print tag raw_print glb_print =
  assert (not @@ PrintMap.mem tag !printers);
  printers := PrintMap.add tag (Print {raw_print; glb_print}) !printers

let apply_printer env sigma level = function
  | Genprint.PrinterBasic pp -> pp env sigma
  | Genprint.PrinterNeedsLevel { default_already_surrounded; printer } ->
    let level = Option.default default_already_surrounded level in
    printer env sigma level

let print_raw env sigma ?level (Raw (tag, v)) =
  let Print {raw_print} = PrintMap.find tag !printers in
  apply_printer env sigma level (raw_print v)

let print_glob env sigma ?level (Glb (tag, v)) =
  let Print {glb_print} = PrintMap.find tag !printers in
  apply_printer env sigma level (glb_print v)

module Subst = struct
  type _ t = Subst : 'glb Gensubst.subst_fun -> (_ * 'glb) t
end

module SubstMap = TDyn.Map(Subst)

let substs = ref SubstMap.empty

let register_subst tag subst =
  assert (not @@ SubstMap.mem tag !substs);
  substs := SubstMap.add tag (Subst subst) !substs

let subst subst (Glb (tag, v)) =
  let Subst f = SubstMap.find tag !substs in
  Glb (tag, f subst v)

module Intern = struct
  (* XXX change type to match how it's called instead of reusing Genintern.intern_fun *)
  type _ t = Intern : ('raw, 'glb) Genintern.intern_fun -> ('raw * 'glb) t
end

module InternMap = TDyn.Map(Intern)

let interns = ref InternMap.empty

let register_intern tag intern =
  assert (not @@ InternMap.mem tag !interns);
  interns := InternMap.add tag (Intern intern) !interns

let intern ?(strict=true) env ?(ltacvars=Id.Set.empty) (Raw (tag, v)) =
  let Intern intern = InternMap.find tag !interns in
  let ist = Genintern.empty_glob_sign ~strict env UnivNames.empty_binders in
  let ist = { ist with ltacvars } in
  let _, v = intern ist v in
  Glb (tag, v)

type 'glb interp_fun = Geninterp.Val.t Id.Map.t -> 'glb -> unit Proofview.tactic

module Interp =
struct
  type _ t = Interp : 'glb interp_fun -> (_ * 'glb) t
end

module InterpMap = TDyn.Map(Interp)

let interps = ref InterpMap.empty

let register_interp tag interp =
  assert (not @@ InterpMap.mem tag !interps);
  interps := InterpMap.add tag (Interp interp) !interps

let interp ?(lfun=Id.Map.empty) (Glb (tag, v)) =
  let Interp interp = InterpMap.find tag !interps in
  interp lfun v

let wit_generic_tactic = Genarg.make0 "generic_tactic"

let () =
  let mkprint f v = Genprint.PrinterBasic (fun env sigma -> f env sigma v) in
  Genprint.register_vernac_print0 wit_generic_tactic (mkprint (print_raw ?level:None));
