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

From Corelib Require Import PosDef micromega_formula micromega_witness.
From Corelib Require Export ring_eval.

Set Implicit Arguments.

Section Feval.
Variables (R : Type) (rO rI : R) (radd rmul rsub: R -> R -> R) (ropp : R -> R).
Variables (Cpow : Type) (Cpow_of_N : N -> Cpow) (rpow : R -> Cpow -> R).
Variables (k : kind) (req rneq rle rlt : R -> R -> eKind k).
Variables (C : Type) (R_of_C : C -> R).
Variables (Env : Type) (env_nth : positive -> Env -> R).

#[local] Abbreviation PEeval := (PEeval
  rO rI radd rmul rsub ropp Cpow_of_N rpow R_of_C env_nth).

Definition eval_op2 (o : Op2) (x y : R) : eKind k :=
  match o with
  | OpEq => req x y
  | OpNEq => rneq x y
  | OpLe => rle x y
  | OpGe => rle y x
  | OpLt => rlt x y
  | OpGt => rlt y x
  end.

Definition Feval (env : Env) (f : Formula C) : eKind k :=
  let 'Build_Formula lhs op rhs := f in
  eval_op2 op (PEeval env lhs) (PEeval env rhs).
End Feval.

Section GFormulaEval.
Variable eqb : bool -> bool -> bool.

Context {TA : Type}. (* type of interpreted atoms *)
Context {TX : kind -> Type}. (* type of uninterpreted terms (Prop) *)
Context {AA : Type}. (* type of annotations for atoms *)
Context {AF : Type}. (* type of formulae identifiers *)

#[local] Abbreviation GFormula := (@GFormula TA TX AA AF).

Variable ex : forall k : kind, TX k -> eKind k. (* [ex] will be the identity *)

Variable ea : forall k : kind, TA -> eKind k.

Definition eTT (k : kind) : eKind k :=
  if k as k' return eKind k' then True else true.

Definition eFF (k : kind) : eKind k :=
  if k as k' return eKind k' then False else false.

Definition eAND (k : kind) : eKind k -> eKind k -> eKind k :=
  if k as k' return eKind k' -> eKind k' -> eKind k' then and else andb.

Definition eOR (k : kind) : eKind k -> eKind k -> eKind k :=
  if k as k' return eKind k' -> eKind k' -> eKind k' then or else orb.

Definition eNOT (k : kind) : eKind k -> eKind k :=
  if k as k' return eKind k' -> eKind k' then not else negb.

Definition eIMPL (k : kind) : eKind k -> eKind k -> eKind k :=
  if k as k' return eKind k' -> eKind k' -> eKind k'
  then (fun x y => x -> y) else implb.

Definition eIFF (k : kind) : eKind k -> eKind k -> eKind k :=
  if k as k' return eKind k' -> eKind k' -> eKind k' then iff else eqb.

Fixpoint GFeval (k : kind) (f : GFormula k) {struct f} : eKind k :=
  match f in micromega_formula.GFormula k' return eKind k' with
  | TT tk => eTT tk
  | FF tk => eFF tk
  | X k p => ex p
  | A k a _ => ea k a
  | @AND _ _ _ _ k e1 e2 => eAND k (GFeval  e1) (GFeval e2)
  | @OR _ _ _ _ k e1 e2 => eOR k (GFeval e1) (GFeval e2)
  | @NOT _ _ _ _ k e => eNOT k (GFeval e)
  | @IMPL _ _ _ _ k f1 _ f2 => eIMPL k (GFeval f1)  (GFeval f2)
  | @IFF _ _ _ _ k f1 f2 => eIFF k (GFeval f1) (GFeval f2)
  | EQ f1 f2 => (GFeval f1) = (GFeval f2)
  end.
End GFormulaEval.

Definition BFeval eqb {A : Type} (ea : forall (k : kind), A -> eKind k)
  (k : kind) (f : BFormula A k) := GFeval eqb (fun k x => x) ea f.

Definition Fmap T T' (f : T -> T') (g : Formula T) : Formula T' :=
  let 'Build_Formula l o r := g in
  Build_Formula (PEmap f l) o (PEmap f r).

Section GFormulaMap.
Context {TA TA' : Type} {TX : kind -> Type} {AA : Type} {AF : Type}.
Fixpoint GFmap (k : kind) (fct : TA -> TA') (f : @GFormula TA TX AA AF k) :
    @GFormula TA' TX AA AF k :=
  match f with
  | TT k => TT k
  | FF k => FF k
  | X k p => X k p
  | A k a t => A k (fct a) t
  | AND f1 f2 => AND (GFmap fct f1) (GFmap fct f2)
  | OR f1 f2 => OR (GFmap fct f1) (GFmap fct f2)
  | NOT f => NOT (GFmap fct f)
  | IMPL f1 a f2 => IMPL (GFmap fct f1) a (GFmap fct f2)
  | IFF f1 f2 => IFF (GFmap fct f1) (GFmap fct f2)
  | EQ f1 f2  => EQ (GFmap fct f1) (GFmap fct f2)
  end.
End GFormulaMap.

Fixpoint Psatz_map T T' (f : T -> T') (e : Psatz T) : Psatz T' :=
  match e with
  | PsatzLet p1 p2 => PsatzLet (Psatz_map f p1) (Psatz_map f p2)
  | PsatzIn _ n => PsatzIn T' n
  | PsatzSquare e => PsatzSquare (Pmap f e)
  | PsatzMulC re e => PsatzMulC (Pmap f re) (Psatz_map f e)
  | PsatzMulE f1 f2 => PsatzMulE (Psatz_map f f1) (Psatz_map f f2)
  | PsatzAdd f1 f2 => PsatzAdd (Psatz_map f f1) (Psatz_map f f2)
  | PsatzC c => PsatzC (f c)
  | PsatzZ _ => PsatzZ T'
  end.
