(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria)                                       *)
(*                                                                      *)
(************************************************************************)

From Corelib Require Import BinNums RatDef micromega_formula micromega_witness.

(** This file provide access to the witness generation tactics
of the micromega OCaml plugin. The following tactics are provided,
where [ffQ : BFormula (Formula Q) isProp]
and [ffZ : BFormula (Formula Z) isProp]:
- wlra_Q wit ffQ : set [wit] to a value of type [list (Psatz Q)]
- wlia wit ffZ : set [wit] to a value of type [list ZArithProof]
- wnia wit ffZ : set [wit] to a value of type [list ZArithProof]
- wnra_Q wit ffQ : set [wit] to a value of type [list (Psatz Q)]
- wsos_Q wit ffQ : set [wit] to a value of type [list (Psatz Q)]
- wsos_Z wit ffZ : set [wit] to a value of type [list ZArithProof]
- wpsatz_Z <n> wit ffZ : set [wit] to a value of type [list ZArithProof]
- wpsatz_Q <n> wit ffQ : set [wit] to a value of type [list (Psatz Q)]
The last four require the external Csdp numerical solver.

Beware that all tactic expect an Ltac name for [wit] and an actual
value for [ff] (not just an identifier). That is, the following works
<<
  pose (ff := ...).
  let ff' := eval unfold ff in ff in wlra_Q wit ff'.
>>
but not
<<
  pose (ff := ...).
  wlra_Q wit ff.
>>
See test-suite/micromega/witness_tactics.v for an example. *)

Declare ML Module "rocq-runtime.plugins.micromega".
