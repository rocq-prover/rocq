(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Corelib Require Import BinNums ring_checker ring_eval field_checker.

Set Implicit Arguments.

Section FEeval.
Variables (P : Type) (ptrue : P) (pneg : P -> P) (pand : P -> P -> P).
Variables (R : Type) (rO rI : R) (radd rmul rsub: R -> R -> R) (ropp : R -> R).
Variables (rdiv : R -> R -> R) (rinv : R -> R).
Variables (Cpow : Type) (Cpow_of_N : N -> Cpow) (rpow : R -> Cpow -> R).
Variables (req : R -> R -> P).
Variables (C : Type) (R_of_C : C -> R).
Variables (Env : Type).
Variables (env_jump : positive -> Env -> Env) (env_nth : positive -> Env -> R).

Fixpoint FEeval l (pe : FExpr C) {struct pe} : R :=
  match pe with
  | FEO => rO
  | FEI => rI
  | FEc c => R_of_C c
  | FEX x => env_nth x l
  | FEadd x y => radd (FEeval l x) (FEeval l y)
  | FEsub x y => rsub (FEeval l x) (FEeval l y)
  | FEmul x y => rmul (FEeval l x) (FEeval l y)
  | FEopp x => ropp (FEeval l x)
  | FEinv x => rinv (FEeval l x)
  | FEdiv x y => rdiv (FEeval l x) (FEeval l y)
  | FEpow x n => rpow (FEeval l x) (Cpow_of_N n)
  end.

#[local] Abbreviation PEeval := (PEeval rO rI radd rmul rsub ropp
  Cpow_of_N rpow R_of_C env_nth).

Fixpoint PCond l (le : list (PExpr C)) {struct le} : P :=
  match le with
  | nil => ptrue
  | cons e1 nil => pneg (req (PEeval l e1) rO)
  | cons e1 l1 => pand (pneg (req (PEeval l e1) rO)) (PCond l l1)
  end.

End FEeval.
Arguments PCond : simpl nomatch.

Fixpoint FEmap T T' (f : T -> T') (e : FExpr T) : FExpr T' :=
  match e with
  | FEO => FEO
  | FEI => FEI
  | FEc c => FEc (f c)
  | FEX p => FEX p
  | FEadd e1 e2 => FEadd (FEmap f e1) (FEmap f e2)
  | FEsub e1 e2 => FEsub (FEmap f e1) (FEmap f e2)
  | FEmul e1 e2 => FEmul (FEmap f e1) (FEmap f e2)
  | FEopp e => FEopp (FEmap f e)
  | FEinv e => FEinv (FEmap f e)
  | FEdiv e1 e2 => FEdiv (FEmap f e1) (FEmap f e2)
  | FEpow e n => FEpow (FEmap f e) n
  end.
