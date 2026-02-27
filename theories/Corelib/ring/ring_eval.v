(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Corelib Require Import BinNums ring_checker.

Set Implicit Arguments.

Section PEeval.
Variables (P : Type) (ptrue : P) (pand : P -> P -> P).
Variables (R : Type) (rO rI : R) (radd rmul rsub: R -> R -> R) (ropp : R -> R).
Variables (Cpow : Type) (Cpow_of_N : N -> Cpow) (rpow : R -> Cpow -> R).
Variables (req : R -> R -> P).
Variables (C : Type) (R_of_C : C -> R).
Variables (Env : Type).
Variables (env_jump : positive -> Env -> Env) (env_nth : positive -> Env -> R).

Fixpoint PEeval l pe : R :=
  match pe with
  | PEO => rO
  | PEI => rI
  | PEc c => R_of_C c
  | PEX _ j => env_nth j l
  | PEadd pe1 pe2 => radd (PEeval l pe1) (PEeval l pe2)
  | PEsub pe1 pe2 => rsub (PEeval l pe1) (PEeval l pe2)
  | PEmul pe1 pe2 => rmul (PEeval l pe1) (PEeval l pe2)
  | PEopp pe1 => ropp (PEeval l pe1)
  | PEpow pe1 n => rpow (PEeval l pe1) (Cpow_of_N n)
  end.

Fixpoint PEeval_eqs l (lpe : list (PExpr C * PExpr C)) : P :=
  match lpe with
  | nil => ptrue
  | cons (me, pe) nil => req (PEeval l me) (PEeval l pe)
  | cons (me, pe) lpe =>
      pand (req (PEeval l me) (PEeval l pe)) (PEeval_eqs l lpe)
  end.

Fixpoint Peval l P : R :=
  match P with
  | Pc c => R_of_C c
  | Pinj j Q => Peval (env_jump j l) Q
  | PX P i Q =>
      radd (rmul (Peval l P) (rpow (env_nth xH l) (Cpow_of_N (Npos i))))
        (Peval (env_jump xH l) Q)
  end.

Fixpoint Meval l M : R :=
  match M with
  | mon0 => rI
  | zmon j M1 => Meval (env_jump j l) M1
  | vmon i M1 =>
      rmul (Meval (env_jump xH l) M1) (rpow (env_nth xH l) (Cpow_of_N (Npos i)))
  end.

Definition cMeval l cM := rmul (R_of_C (fst cM)) (Meval l (snd cM)).
End PEeval.

Fixpoint PEmap T T' (f : T -> T') (e : PExpr T) : PExpr T' :=
  match e with
  | PEO => PEO
  | PEI => PEI
  | PEc c => PEc (f c)
  | PEX _ p => PEX _ p
  | PEadd e1 e2 => PEadd (PEmap f e1) (PEmap f e2)
  | PEsub e1 e2 => PEsub (PEmap f e1) (PEmap f e2)
  | PEmul e1 e2 => PEmul (PEmap f e1) (PEmap f e2)
  | PEopp e => PEopp (PEmap f e)
  | PEpow e n => PEpow (PEmap f e) n
  end.

Fixpoint Pmap T T' (f : T -> T') (P : Pol T) : Pol T' :=
  match P with
  | Pc c => Pc (f c)
  | Pinj j P => Pinj j (Pmap f P)
  | PX P i Q => PX (Pmap f P) i (Pmap f Q)
  end.
