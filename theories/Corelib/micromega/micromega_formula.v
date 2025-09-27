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
(* Micromega : A reflexive tactic using the Positivstellensatz          *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2019                             *)
(*                                                                      *)
(************************************************************************)

From Corelib Require Import PosDef.
From Corelib Require Export ring_checker.

Set Implicit Arguments.

Register PEc as micromega.PExpr.PEc.
Register PEX as micromega.PExpr.PEX.
Register PEadd as micromega.PExpr.PEadd.
Register PEsub as micromega.PExpr.PEsub.
Register PEmul as micromega.PExpr.PEmul.
Register PEopp as micromega.PExpr.PEopp.
Register PEpow as micromega.PExpr.PEpow.

Variant Op2 : Set := (** binary relations *)
| OpEq
| OpNEq
| OpLe
| OpGe
| OpLt
| OpGt.

Register OpEq as micromega.Op2.OpEq.
Register OpNEq as micromega.Op2.OpNEq.
Register OpLe as micromega.Op2.OpLe.
Register OpGe as micromega.Op2.OpGe.
Register OpLt as micromega.Op2.OpLt.
Register OpGt as micromega.Op2.OpGt.

#[universes(template)]
Record Formula (T : Type) : Type := Build_Formula {
  Flhs : PExpr T;
  Fop : Op2;
  Frhs : PExpr T
}.

Register Formula as micromega.Formula.type.
Register Build_Formula as micromega.Formula.Build_Formula.

(** Formulae are either interpreted over Prop or bool. *)
Variant kind : Type := isProp | isBool.

Register isProp as micromega.kind.isProp.
Register isBool as micromega.kind.isBool.

Section S.
Context {TA : Type}. (** type of interpreted atoms *)
Context {TX : kind -> Type}. (** type of uninterpreted terms (Prop) *)
Context {AA : Type}. (** type of annotations for atoms *)
Context {AF : Type}. (** type of formulae identifiers *)

Inductive GFormula : kind -> Type :=
| TT : forall (k : kind), GFormula k
| FF : forall (k : kind), GFormula k
| X : forall (k : kind), TX k -> GFormula k
| A : forall (k : kind), TA -> AA -> GFormula k
| AND : forall (k : kind), GFormula k -> GFormula k -> GFormula k
| OR : forall (k : kind), GFormula k -> GFormula k -> GFormula k
| NOT : forall (k : kind), GFormula k -> GFormula k
| IMPL : forall (k : kind), GFormula k -> option AF -> GFormula k -> GFormula k
| IFF : forall (k : kind), GFormula k -> GFormula k -> GFormula k
| EQ : GFormula isBool -> GFormula isBool -> GFormula isProp.
End S.

Register TT as micromega.GFormula.TT.
Register FF as micromega.GFormula.FF.
Register X as micromega.GFormula.X.
Register A as micromega.GFormula.A.
Register AND as micromega.GFormula.AND.
Register OR as micromega.GFormula.OR.
Register NOT as micromega.GFormula.NOT.
Register IMPL as micromega.GFormula.IMPL.
Register IFF as micromega.GFormula.IFF.
Register EQ as micromega.GFormula.EQ.

Definition eKind (k : kind) := if k then Prop else bool.

Register eKind as micromega.eKind.

(** Typical boolean formulae *)
Definition BFormula (A : Type) := @GFormula A eKind unit unit.

Register BFormula as micromega.BFormula.type.
