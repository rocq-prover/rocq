(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Corelib Require Import BinNums RatDef.
From Corelib Require Export ring_checker.

Set Implicit Arguments.

Register Pc as micromega.Pol.Pc.
Register Pinj as micromega.Pol.Pinj.
Register PX as micromega.Pol.PX.

Inductive Psatz (C : Type) : Type :=
| PsatzLet: Psatz C -> Psatz C -> Psatz C
| PsatzIn : nat -> Psatz C
| PsatzSquare : Pol C -> Psatz C
| PsatzMulC : Pol C -> Psatz C -> Psatz C
| PsatzMulE : Psatz C -> Psatz C -> Psatz C
| PsatzAdd : Psatz C -> Psatz C -> Psatz C
| PsatzC : C -> Psatz C
| PsatzZ : Psatz C.

Register PsatzLet as micromega.Psatz.PsatzLet.
Register PsatzIn as micromega.Psatz.PsatzIn.
Register PsatzSquare as micromega.Psatz.PsatzSquare.
Register PsatzMulC as micromega.Psatz.PsatzMulC.
Register PsatzMulE as micromega.Psatz.PsatzMulE.
Register PsatzAdd as micromega.Psatz.PsatzAdd.
Register PsatzC as micromega.Psatz.PsatzC.
Register PsatzZ as micromega.Psatz.PsatzZ.

Definition QWitness := Psatz Q.

Register QWitness as micromega.QWitness.type.

Definition ZWitness := Psatz Z.

Inductive ZArithProof :=
| DoneProof
| RatProof : ZWitness -> ZArithProof -> ZArithProof
| CutProof : ZWitness -> ZArithProof -> ZArithProof
| SplitProof : Pol Z -> ZArithProof -> ZArithProof -> ZArithProof
| EnumProof : ZWitness -> ZWitness -> list ZArithProof -> ZArithProof
| ExProof : positive -> ZArithProof -> ZArithProof
(*ExProof x : exists z t, x = z - t /\ z >= 0 /\ t >= 0 *)
.

Register ZArithProof as micromega.ZArithProof.type.
Register DoneProof as micromega.ZArithProof.DoneProof.
Register RatProof as micromega.ZArithProof.RatProof.
Register CutProof as micromega.ZArithProof.CutProof.
Register SplitProof as micromega.ZArithProof.SplitProof.
Register EnumProof as micromega.ZArithProof.EnumProof.
Register ExProof as micromega.ZArithProof.ExProof.
