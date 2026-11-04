(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Declarations

let axiom_free = ref false

let flags_are_safe flags =
  flags.check_guarded && flags.check_positive && flags.check_universes &&
  flags.check_eliminations && not flags.allow_uip

let check_axiom_free flags =
  if !axiom_free && not (flags_are_safe flags) then
    CErrors.user_err Pp.(str "Axioms or unsafe features found (-axiom-free).")

let set_local_flags flags env =
  (* Explicitly ignored flags are set to not change *)
  let envflags = Environ.typing_flags env in
  let flags = {
    (* These flags may be overridden *)
    check_guarded = flags.check_guarded;
    check_positive = flags.check_positive;
    check_universes = flags.check_universes;
    check_eliminations = flags.check_eliminations;
    conv_oracle = flags.conv_oracle;
    share_reduction = flags.share_reduction;
    unfold_dep_heuristic = flags.unfold_dep_heuristic;
    unfold_height_heuristic = flags.unfold_height_heuristic;
    allow_uip = flags.allow_uip;
    (* These flags may not *)
    enable_VM = envflags.enable_VM;
    enable_native_compiler = envflags.enable_native_compiler;
    indices_matter = envflags.indices_matter;
    impredicative_set = envflags.impredicative_set;
    sprop_allowed = envflags.sprop_allowed;
  }
  in
  Environ.set_typing_flags flags env

(* Set from the -bytecode-compiler command line option. The checker consults
   this rather than the environment's flag when deciding whether to recompile
   the VM bytecode of a library. *)
let enable_vm = ref false

let is_axiom_free env axioms =
  let primitive c = Environ.is_primitive_type env (Names.Constant.make1 c) in
  List.for_all primitive axioms && not (Environ.rewrite_rules_allowed env)
