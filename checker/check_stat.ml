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
open Names
open Environ
open Mod_checking

let memory_stat = ref false

let print_memory_stat () =
  if !memory_stat then begin
    Format.printf "total heap size = %d kbytes\n" (CObj.heap_size_kb ());
    Format.print_newline();
    Format.print_flush()
  end

let pr_impredicative_set env =
  if is_impredicative_set env then str "Theory: Set is impredicative"
  else str "Theory: Set is predicative"

let pr_rewrite_rules env =
  if rewrite_rules_allowed env then str "Theory: Rewrite rules are allowed (consistency, subject reduction, confluence and normalization might be broken)"
  else str "Theory: Rewrite rules are not allowed"

let pr_assumptions ?(skip_if_empty=false) ass axs =
  match axs with
  | [] ->
    if skip_if_empty then mt()
    else
      str "* " ++ str ass ++ str ": <none>"
  | _ :: _ ->
    str "* " ++ v 2 (str ass ++ str ":" ++ spc() ++ prlist_with_sep spc KerName.print axs)

let pr_axioms axioms =
  let csts = KerName.Set.elements axioms.undef in
  pr_assumptions "Axioms" csts

let get_unsafe p axioms =
  KerName.Map.fold (fun kn flags acc -> if p flags then kn::acc else acc)
    axioms.unsafe_flags
    []

let pr_unsafe ?skip_if_empty hdr p axioms =
  let l = get_unsafe p axioms in
  pr_assumptions ?skip_if_empty hdr l

let pr_type_in_type axioms =
  pr_unsafe "Constants/Inductives relying on type-in-type"
    (fun flags -> flags.typeintype) axioms

(* Kept out of the report when empty: this flag has no vernacular setter and
   should stay obscure (see #22294 discussion). *)
let pr_unchecked_eliminations axioms =
  pr_unsafe ~skip_if_empty:true "Constants/Inductives relying on unchecked sort eliminations"
    (fun flags -> flags.badelims) axioms

let pr_unguarded axioms =
  pr_unsafe "Constants/Inductives relying on unsafe (co)fixpoints"
    (fun flags -> flags.unguarded) axioms

let pr_nonpositive axioms =
  pr_unsafe "Inductives whose positivity is assumed"
    (fun flags -> flags.nonpositive) axioms

let pr_indices_matter axioms =
  pr_unsafe "Inductives relying on indices not mattering"
    (fun flags -> flags.indices_nomatter) axioms

(* rare option, not printed when empty *)
let pr_uip axioms =
  pr_unsafe ~skip_if_empty:true "Inductives relying on Definitional UIP"
    (fun flags -> flags.uip) axioms

let print_context env axioms = match axioms with
| None -> ()
| Some axioms ->
  let axioms = [
    pr_axioms axioms;
    pr_type_in_type axioms;
    pr_unchecked_eliminations axioms;
    pr_unguarded axioms;
    pr_nonpositive axioms;
    pr_indices_matter axioms;
    pr_uip axioms;
  ]
  in
  let axioms = List.filter (fun pp -> not (Pp.ismt pp)) axioms in
  Feedback.msg_notice
    (hov 0
    (fnl() ++ str"CONTEXT SUMMARY" ++ fnl() ++
    str"===============" ++ fnl() ++ fnl() ++
    str "* " ++ hov 0 (pr_impredicative_set env) ++ fnl() ++ fnl() ++
    str "* " ++ hov 0 (pr_rewrite_rules env) ++ fnl() ++ fnl() ++
    prlist_with_sep (fun () -> fnl() ++ fnl()) Fun.id axioms)
    )

let stats env axioms =
  print_context env axioms;
  print_memory_stat ()
