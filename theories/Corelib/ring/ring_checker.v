(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Corelib Require Import PosDef IntDef.

Set Implicit Arguments.

(** The ring tactic is a decision procedure for ring equalities.
See [ring_checker] at the end of the file for the main definition.
This file contains the computational part of the ring tactic, to get a full
tactic, one needs in addition an input term reifier, a proof of correctness
of the computational part and a tactic gluing everything together. *)

(** Definition of polynomial expressions *)
Inductive PExpr {C} : Type :=
| PEO : PExpr
| PEI : PExpr
| PEc : C -> PExpr
| PEX : positive -> PExpr
| PEadd : PExpr -> PExpr -> PExpr
| PEsub : PExpr -> PExpr -> PExpr
| PEmul : PExpr -> PExpr -> PExpr
| PEopp : PExpr -> PExpr
| PEpow : PExpr -> N -> PExpr.
Arguments PExpr : clear implicits.
Arguments PEX : clear implicits.

(** Definition of multivariable polynomials with coefficients in C :
Type [Pol] represents [X1 ... Xn].
The representation is Horner's where a [n] variable polynomial
(C[X1..Xn]) is seen as a polynomial on [X1] whose coefficients
are polynomials with [n-1] variables (C[X2..Xn]).
There are several optimisations to make the repr more compact:
- [Pc c] is the constant polynomial of value c
   == c*X1^0*..*Xn^0
- [Pinj j Q] is a polynomial constant w.r.t the [j] first variables.
    variable indices are shifted of j in Q.
   == X1^0 *..* Xj^0 * Q{X1 <- Xj+1;..; Xn-j <- Xn}
- [PX P i Q] is an optimised Horner form of P*X^i + Q
    with P not the null polynomial
   == P * X1^i + Q{X1 <- X2; ..; Xn-1 <- Xn}
In addition:
- polynomials of the form (PX (PX P i (Pc 0)) j Q) are forbidden
  since they can be represented by the simpler form (PX P (i+j) Q)
- (Pinj i (Pinj j P)) is (Pinj (i+j) P)
- (Pinj i (Pc c)) is (Pc c) *)
Inductive Pol {C} : Type :=
| Pc : C -> Pol
| Pinj : positive -> Pol -> Pol
| PX : Pol -> positive -> Pol -> Pol.
Arguments Pol : clear implicits.

(** A monomial is X1^k1...Xi^ki. Its representation
is a simplified version of the polynomial representation:
- [mon0] correspond to the polynom [P1].
- [(zmon j M)] corresponds to [(Pinj j ...)],
  i.e. skip j variable indices.
- [(vmon i M)] is X^i*M with X the current variable,
  its corresponds to (PX P1 i ...)] *)
Inductive Mon : Set :=
| mon0 : Mon
| zmon : positive -> Mon -> Mon
| vmon : positive -> Mon -> Mon.

(** * Basic arithmetic operations on Horner polynomials [Pol]

One can prove that an eval function [Peval] commutes with
each operation, e.g., [Peval l (Padd P P') = Peval l P + Peval l P'] *)
Section PolOps.

(** Coefficients *)
Variable (C : Type) (cO cI : C) (cadd cmul csub : C -> C -> C) (copp : C -> C).
Variable ceqb : C -> C -> bool.

Implicit Type P : Pol C.

(** Equality *)
Fixpoint Peq P P' {struct P'} : bool :=
  match P, P' with
  | Pc c, Pc c' => ceqb c c'
  | Pinj j Q, Pinj j' Q' =>
      match Pos.compare j j' with
      | Eq => Peq Q Q'
      | _ => false
      end
  | PX P i Q, PX P' i' Q' =>
      match Pos.compare i i' with
      | Eq => if Peq P P' then Peq Q Q' else false
      | _ => false
      end
  | _, _ => false
  end.

(** Constructors *)

Definition P0 := Pc cO.
Definition P1 := Pc cI.

Definition mkPinj j P :=
  match P with
  | Pc _ => P
  | Pinj j' Q => Pinj (Pos.add j j') Q
  | _ => Pinj j P
  end.

Definition mkPinj_pred j P :=
  match j with
  | xH => P
  | xO j => Pinj (Pos.pred_double j) P
  | xI j => Pinj (xO j) P
  end.

Definition mkX j := mkPinj_pred j (PX P1 1 P0).

Definition mkPX P i Q :=
  match P with
  | Pc c => if ceqb c cO then mkPinj xH Q else PX P i Q
  | Pinj _ _ => PX P i Q
  | PX P' i' Q' => if Peq Q' P0 then PX P' (Pos.add i' i) Q else PX P i Q
  end.

(** Opposite *)
Fixpoint Popp P : Pol C :=
  match P with
  | Pc c => Pc (copp c)
  | Pinj j Q => Pinj j (Popp Q)
  | PX P i Q => PX (Popp P) i (Popp Q)
  end.

(** Addition and subtraction *)

Fixpoint PaddC P c : Pol C :=
  match P with
  | Pc c1 => Pc (cadd c1 c)
  | Pinj j Q => Pinj j (PaddC Q c)
  | PX P i Q => PX P i (PaddC Q c)
  end.

Fixpoint PsubC P c : Pol C :=
  match P with
  | Pc c1 => Pc (csub c1 c)
  | Pinj j Q => Pinj j (PsubC Q c)
  | PX P i Q => PX P i (PsubC Q c)
  end.

Section PopI.
Variable Pop : Pol C -> Pol C -> Pol C.
Variable Q : Pol C.

(** [P + Pinj j Q], assuming [Pop . Q] is [. + Q] *)
Fixpoint PaddI (j : positive) P : Pol C :=
  match P with
  | Pc c => mkPinj j (PaddC Q c)
  | Pinj j' Q' =>
      match Z.pos_sub j' j with
      | Zpos k =>  mkPinj j (Pop (Pinj k Q') Q)
      | Z0 => mkPinj j (Pop Q' Q)
      | Zneg k => mkPinj j' (PaddI k Q')
      end
  | PX P i Q' =>
      match j with
      | xH => PX P i (Pop Q' Q)
      | xO j => PX P i (PaddI (Pos.pred_double j) Q')
      | xI j => PX P i (PaddI (xO j) Q')
      end
  end.

(** [P - Pinj j Q], assuming [Pop . Q] is [. - Q] *)
Fixpoint PsubI (j : positive) P : Pol C :=
  match P with
  | Pc c => mkPinj j (PaddC (Popp Q) c)
  | Pinj j' Q' =>
      match Z.pos_sub j' j with
      | Zpos k =>  mkPinj j (Pop (Pinj k Q') Q)
      | Z0 => mkPinj j (Pop Q' Q)
      | Zneg k => mkPinj j' (PsubI k Q')
      end
  | PX P i Q' =>
      match j with
      | xH => PX P i (Pop Q' Q)
      | xO j => PX P i (PsubI (Pos.pred_double j) Q')
      | xI j => PX P i (PsubI (xO j) Q')
      end
  end.

Variable P' : Pol C.

(** [P + PX P' i' P0], assuming [Pop . P'] is [. + P'] *)
Fixpoint PaddX (i' : positive) P : Pol C :=
  match P with
  | Pc c => PX P' i' P
  | Pinj j Q' =>
      match j with
      | xH =>  PX P' i' Q'
      | xO j => PX P' i' (Pinj (Pos.pred_double j) Q')
      | xI j => PX P' i' (Pinj (xO j) Q')
      end
  | PX P i Q' =>
      match Z.pos_sub i i' with
      | Zpos k => mkPX (Pop (PX P k P0) P') i' Q'
      | Z0 => mkPX (Pop P P') i Q'
      | Zneg k => mkPX (PaddX k P) i Q'
      end
  end.

(** [P - PX P' i' P0], assuming [Pop . P'] is [. - P'] *)
Fixpoint PsubX (i' : positive) P : Pol C :=
  match P with
  | Pc c => PX (Popp P') i' P
  | Pinj j Q' =>
      match j with
      | xH =>  PX (Popp P') i' Q'
      | xO j => PX (Popp P') i' (Pinj (Pos.pred_double j) Q')
      | xI j => PX (Popp P') i' (Pinj (xO j) Q')
      end
  | PX P i Q' =>
      match Z.pos_sub i i' with
      | Zpos k => mkPX (Pop (PX P k P0) P') i' Q'
      | Z0 => mkPX (Pop P P') i Q'
      | Zneg k => mkPX (PsubX k P) i Q'
      end
  end.
End PopI.

Fixpoint Padd P P' {struct P'} : Pol C :=
  match P' with
  | Pc c' => PaddC P c'
  | Pinj j' Q' => PaddI Padd Q' j' P
  | PX P' i' Q' =>
      match P with
      | Pc c => PX P' i' (PaddC Q' c)
      | Pinj j Q =>
          match j with
          | xH => PX P' i' (Padd Q Q')
          | xO j => PX P' i' (Padd (Pinj (Pos.pred_double j) Q) Q')
          | xI j => PX P' i' (Padd (Pinj (xO j) Q) Q')
          end
      | PX P i Q =>
          match Z.pos_sub i i' with
          | Zpos k => mkPX (Padd (PX P k P0) P') i' (Padd Q Q')
          | Z0 => mkPX (Padd P P') i (Padd Q Q')
          | Zneg k => mkPX (PaddX Padd P' k P) i (Padd Q Q')
          end
      end
  end.

Fixpoint Psub P P' {struct P'} : Pol C :=
  match P' with
  | Pc c' => PsubC P c'
  | Pinj j' Q' => PsubI Psub Q' j' P
  | PX P' i' Q' =>
      match P with
      | Pc c => PX (Popp P') i' (PaddC (Popp Q') c)
      | Pinj j Q =>
          match j with
          | xH => PX (Popp P') i' (Psub Q Q')
          | xO j => PX (Popp P') i' (Psub (Pinj (Pos.pred_double j) Q) Q')
          | xI j => PX (Popp P') i' (Psub (Pinj (xO j) Q) Q')
          end
      | PX P i Q =>
          match Z.pos_sub i i' with
          | Zpos k => mkPX (Psub (PX P k P0) P') i' (Psub Q Q')
          | Z0 => mkPX (Psub P P') i (Psub Q Q')
          | Zneg k => mkPX (PsubX Psub P' k P) i (Psub Q Q')
          end
      end
  end.

(** Multiplication *)

Fixpoint PmulC_aux P c : Pol C :=
  match P with
  | Pc c' => Pc (cmul c' c)
  | Pinj j Q => mkPinj j (PmulC_aux Q c)
  | PX P i Q => mkPX (PmulC_aux P c) i (PmulC_aux Q c)
  end.

Definition PmulC P c :=
  if ceqb c cO then P0 else
  if ceqb c cI then P else PmulC_aux P c.

(** [P * Pinj j Q], assuming [Pmul . Q] is [. * Q] *)
Section PmulI.
Variable Pmul : Pol C -> Pol C -> Pol C.
Variable Q : Pol C.
Fixpoint PmulI (j : positive) P : Pol C :=
  match P with
  | Pc c => mkPinj j (PmulC Q c)
  | Pinj j' Q' =>
      match Z.pos_sub j' j with
      | Zpos k => mkPinj j (Pmul (Pinj k Q') Q)
      | Z0 => mkPinj j (Pmul Q' Q)
      | Zneg k => mkPinj j' (PmulI k Q')
      end
  | PX P' i' Q' =>
      match j with
      | xH => mkPX (PmulI xH P') i' (Pmul Q' Q)
      | xO j' => mkPX (PmulI j P') i' (PmulI (Pos.pred_double j') Q')
      | xI j' => mkPX (PmulI j P') i' (PmulI (xO j') Q')
      end
   end.
End PmulI.

Fixpoint Pmul P P'' {struct P''} : Pol C :=
  match P'' with
  | Pc c => PmulC P c
  | Pinj j' Q' => PmulI Pmul Q' j' P
  | PX P' i' Q' =>
      match P with
      | Pc c => PmulC P'' c
      | Pinj j Q =>
          let QQ' :=
            match j with
            | xH => Pmul Q Q'
            | xO j => Pmul (Pinj (Pos.pred_double j) Q) Q'
            | xI j => Pmul (Pinj (xO j) Q) Q'
            end in
          mkPX (Pmul P P') i' QQ'
      | PX P i Q=>
          let QQ' := Pmul Q Q' in
          let PQ' := PmulI Pmul Q' xH P in
          let QP' := Pmul (mkPinj xH Q) P' in
          let PP' := Pmul P P' in
          Padd (mkPX (Padd (mkPX PP' i P0) QP') i' P0) (mkPX PQ' i QQ')
      end
  end.

Fixpoint Psquare P : Pol C :=
  match P with
  | Pc c => Pc (cmul c c)
  | Pinj j Q => Pinj j (Psquare Q)
  | PX P i Q =>
      let twoPQ := Pmul P (mkPinj xH (PmulC Q (cadd cI cI))) in
      let Q2 := Psquare Q in
      let P2 := Psquare P in
      mkPX (Padd (mkPX P2 i P0) twoPQ) i Q2
  end.

Fixpoint Ppow_pos (res P : Pol C) (p : positive) : Pol C :=
  match p with
  | xH => Pmul res P
  | xO p => Ppow_pos (Ppow_pos res P p) P p
  | xI p => Pmul (Ppow_pos (Ppow_pos res P p) P p) P
  end.

Definition Ppow_N P n := match n with N0 => P1 | Npos p => Ppow_pos P1 P p end.

End PolOps.

Section MonOps.

(** Coefficients *)
Variable (C : Type) (cO cI : C) (cadd cmul : C -> C -> C).
Variable (ceqb : C -> C -> bool) (cdiv : C -> C -> C * C).
(* only requirement on cdiv is:
[forall x y, let (q, r) := cdiv x y in x = y * q + r] *)

Implicit Type P : Pol C.
Implicit Type M : Mon.

#[local] Abbreviation Peq := (Peq ceqb).
#[local] Abbreviation P0 := (P0 cO).
#[local] Abbreviation mkPX := (mkPX cO ceqb).
#[local] Abbreviation Padd := (Padd cO cadd ceqb).
#[local] Abbreviation Pmul := (Pmul cO cI cadd cmul ceqb).

(** Constructors *)

Definition mkZmon j M := match M with mon0 => mon0 | _ => zmon j M end.

Definition zmon_pred j M :=
  match j with xH => M | _ => mkZmon (Pos.pred j) M end.

Definition mkVmon i M :=
  match M with
  | mon0 => vmon i mon0
  | zmon j m => vmon i (zmon_pred j m)
  | vmon i' m => vmon (Pos.add i i') m
  end.

(** [forall l P c, let (Q, R) := CFactor P c in
Peval l P = Peval l Q + R_of_C c * Peval l R] *)
Fixpoint CFactor P (c : C) {struct P} : Pol C * Pol C :=
  match P with
  | Pc c1 => let (q, r) := cdiv c1 c in (Pc r, Pc q)
  | Pinj j1 P1 =>
      let (R, S) := CFactor P1 c in
      (mkPinj j1 R, mkPinj j1 S)
  | PX P1 i Q1 =>
      let (R1, S1) := CFactor P1 c in
      let (R2, S2) := CFactor Q1 c in
      (mkPX R1 i R2, mkPX S1 i S2)
  end.

(** [forall l P c M, let (Q, R) := MFactor P c M in
Peval l P = Peval l Q + cMeval l (c, M) * Peval l R] *)
Fixpoint MFactor P c (M : Mon) {struct P} : Pol C * Pol C :=
  match P, M with
  | _, mon0 => if ceqb c cI then (Pc cO, P) else CFactor P c
  | Pc _, _    => (P, Pc cO)
  | Pinj j1 P1, zmon j2 M1 =>
      match Pos.compare j1 j2 with
      | Eq => let (R, S) := MFactor P1 c M1 in (mkPinj j1 R, mkPinj j1 S)
      | Lt =>
          let (R, S) := MFactor P1 c (zmon (Pos.sub j2 j1) M1) in
          (mkPinj j1 R, mkPinj j1 S)
      | Gt => (P, Pc cO)
      end
  | Pinj _ _, vmon _ _ => (P, Pc cO)
  | PX P1 i Q1, zmon j M1 =>
      let M2 := zmon_pred j M1 in
      let (R1, S1) := MFactor P1 c M in
      let (R2, S2) := MFactor Q1 c M2 in
      (mkPX R1 i R2, mkPX S1 i S2)
  | PX P1 i Q1, vmon j M1 =>
      match Pos.compare i j with
      | Eq => let (R1, S1) := MFactor P1 c (mkZmon xH M1) in (mkPX R1 i Q1, S1)
      | Lt =>
          let (R1, S1) := MFactor P1 c (vmon (Pos.sub j i) M1) in
          (mkPX R1 i Q1, S1)
      | Gt =>
          let (R1, S1) := MFactor P1 c (mkZmon xH M1) in
          (mkPX R1 i Q1, mkPX S1 (Pos.sub i j) (Pc cO))
      end
  end.

(** [forall l P1 cM1 P2 P3, POneSubst P1 cM1 P2 = Some P3 ->
cMeval l cM1 = Peval l P2 -> Peval l P1 = Peval l P3] *)
Definition POneSubst P1 (cM1 : C * Mon) P2 : option (Pol C) :=
  let (c, M1) := cM1 in
  let (Q1, R1) := MFactor P1 c M1 in
  match R1 with
  | (Pc c) => if ceqb c cO then None else Some (Padd Q1 (Pmul P2 R1))
  | _ => Some (Padd Q1 (Pmul P2 R1))
  end.

(** [forall l n P1 cM1 P2, cMeval l cM1 = Peval l P2 ->
Peval l P1 = Peval l (PNSubst1 P1 cM1 P2 n)] *)
Fixpoint PNSubst1 P1 (cM1 : C * Mon) P2 n : Pol C :=
  match POneSubst P1 cM1 P2 with
  | Some P3 => match n with S n1 => PNSubst1 P3 cM1 P2 n1 | O => P3 end
  | None => P1
  end.

(** [forall l n P1 cM1 P2 P3, PNSubst P1 cM1 P2 n = Some P3 ->
cMeval l cM1 = Peval l P2 -> Peval l P1 = Peval l P3] *)
Definition PNSubst P1 (cM1 : C * Mon) P2 n : option (Pol C) :=
  match POneSubst P1 cM1 P2 with
  | Some P3 => match n with S n1 => Some (PNSubst1 P3 cM1 P2 n1) | _ => None end
  | None => None
  end.

(** [forall l n LM1 P1, all (fun MP => cMeval l MP.1 = Peval l MP.2) LM1 ->
Peval l P1 = Peval l (PSubstL1 P1 LM1 n)] *)
Fixpoint PSubstL1 P1 (LM1 : list ((C * Mon) * Pol C)) n : Pol C :=
  match LM1 with
  | cons (M1, P2) LM2 => PSubstL1 (PNSubst1 P1 M1 P2 n) LM2 n
  | nil => P1
  end.

(** [forall l n LM1 P1 P2, PSubstL P1 LM1 n = Some P2 ->
  all (fun MP => cMeval l MP.1 = Peval l MP.2) LM1 ->
Peval l P1 = Peval l P2] *)
Fixpoint PSubstL P1 (LM1 : list ((C * Mon) * Pol C)) n : option (Pol C) :=
  match LM1 with
  | cons (M1, P2) LM2 =>
      match PNSubst P1 M1 P2 n with
      | Some P3 => Some (PSubstL1 P3 LM2 n)
      | None => PSubstL P1 LM2 n
      end
  | nil => None
  end.

(** [forall l m n LM1 P1,
  all (fun MP => cMeval l MP.1 = Peval l MP.2) LM1 ->
Peval l P1 = Peval l (PNSubstL P1 LM1 m n)] *)
Fixpoint PNSubstL P1 (LM1: list ((C * Mon) * Pol C)) m n : Pol C :=
  match PSubstL P1 LM1 n with
  | Some P3 => match m with S m1 => PNSubstL P3 LM1 m1 n | O => P3 end
  | None => P1
  end.

(** [forall l P m, Mon_of_Pol P = Some m -> cMeval l m = Peval l P] *)
Fixpoint Mon_of_Pol P : option (C * Mon) :=
  match P with
  | Pc c => if ceqb c cO then None else Some (c, mon0)
  | Pinj j P =>
      match Mon_of_Pol P with
      | None => None
      | Some (c,m) =>  Some (c, mkZmon j m)
      end
  | PX P i Q =>
      if Peq Q P0 then
        match Mon_of_Pol P with
        | None => None
        | Some (c, m) => Some (c, mkVmon i m)
        end
      else None
  end.

End MonOps.

(** * Checker for the ring tactic *)
Section RingChecker.

Variables (C : Type) (cO cI : C) (cadd cmul csub : C -> C -> C) (copp : C -> C).
Variables (ceqb : C -> C -> bool) (cdiv : C -> C -> C * C).
(* only requirement on cdiv is:
[forall x y, let (q, r) := cdiv x y in x = y * q + r] *)

#[local] Abbreviation P0 := (P0 cO).
#[local] Abbreviation P1 := (P1 cI).
#[local] Abbreviation mkX := (mkX cO cI).
#[local] Abbreviation Peq := (Peq ceqb).
#[local] Abbreviation Popp := (Popp copp).
#[local] Abbreviation Padd := (Padd cO cadd ceqb).
#[local] Abbreviation Psub := (Psub cO cadd csub copp ceqb).
#[local] Abbreviation Pmul := (Pmul cO cI cadd cmul ceqb).
#[local] Abbreviation Ppow_N := (Ppow_N cO cI cadd cmul ceqb).
#[local] Abbreviation PNSubstL := (PNSubstL cO cI cadd cmul ceqb cdiv).
#[local] Abbreviation Mon_of_Pol := (Mon_of_Pol cO ceqb).

(** [forall l pe, Peval l (Pol_of_Pexpr pe) = PEeval l pe] *)
Fixpoint Pol_of_PExpr (pe : PExpr C) : Pol C :=
  match pe with
  | PEO => P0
  | PEI => P1
  | PEc c => Pc c
  | PEX _ j => mkX j
  | PEadd (PEopp pe1) pe2 => Psub (Pol_of_PExpr pe2) (Pol_of_PExpr pe1)
  | PEadd pe1 (PEopp pe2) => Psub (Pol_of_PExpr pe1) (Pol_of_PExpr pe2)
  | PEadd pe1 pe2 => Padd (Pol_of_PExpr pe1) (Pol_of_PExpr pe2)
  | PEsub pe1 pe2 => Psub (Pol_of_PExpr pe1) (Pol_of_PExpr pe2)
  | PEmul pe1 pe2 => Pmul (Pol_of_PExpr pe1) (Pol_of_PExpr pe2)
  | PEopp pe1 => Popp (Pol_of_PExpr pe1)
  | PEpow pe1 n => Ppow_N (Pol_of_PExpr pe1) n
  end.

(** [forall n l lpe pe,
  all (fun PP => PEeval l PP.1 = PEeval l PP.2) lpe ->
Peval l (norm_subst n (mk_monpol_list lpe) pe) = PEeval l pe] *)
Definition norm_subst (n : nat) (lmp : list (C * Mon * Pol C)) pe :=
  PNSubstL (Pol_of_PExpr pe) lmp n n.

(** [forall l lpe,
  all (fun PP => PEeval l PP.1 = PEeval l PP.2) lpe ->
all (fun MP => cMeval l MP.1 = Peval l MP.2) (mk_monpol_list lpe)] *)
Fixpoint mk_monpol_list (lpe : list (PExpr C * PExpr C)) :
    list (C * Mon * Pol C) :=
  match lpe with
  | nil => nil
  | cons (me, pe) lpe =>
      match Mon_of_Pol (norm_subst 0 nil me) with
      | None => mk_monpol_list lpe
      | Some m => (m, norm_subst 0 nil pe) :: mk_monpol_list lpe
      end
  end.

(** [forall n l lpe pe1 pe2, PEeval_eqs l lpe -> ring_checker n lpe pe1 pe2 ->
PEeval l pe1 = PEeval l pe2] *)
Definition ring_checker n lpe pe1 pe2 :=
  let lmp := mk_monpol_list lpe in
  Peq (norm_subst n lmp pe1) (norm_subst n lmp pe2).

End RingChecker.

(** a trivial implementation for cdiv *)
Definition triv_div (C : Type) (cO cI : C) (ceqb : C -> C -> bool) x y :=
  if ceqb x y then (cI, cO) else (cO, x).
