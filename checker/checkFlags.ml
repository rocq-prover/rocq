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

type unsafe_flags = {
  unguarded : bool;
  nonpositive : bool;
  typeintype : bool;
  badelims : bool;
  indices_nomatter : bool;
  uip : bool;
}

let flags_are_safe ~isind flags =
  let indices_nomatter = match isind with
    | None -> false
    | Some mib ->
      not flags.indices_matter &&
      Array.exists (fun mip -> mip.mind_relies_on_indices_not_mattering) mib.mind_packets
  in
  let unsafe = {
    unguarded = not flags.check_guarded;
    nonpositive = not flags.check_positive && Option.has_some isind;
    typeintype = not flags.check_universes;
    badelims = not flags.check_eliminations;
    indices_nomatter;
    uip = flags.allow_uip && Option.has_some isind;
  }
  in
  if unsafe.unguarded || unsafe.nonpositive || unsafe.typeintype || unsafe.badelims ||
     indices_nomatter || unsafe.uip
  then Some unsafe
  else None

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
    cumulativity_zeta = flags.cumulativity_zeta;
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
