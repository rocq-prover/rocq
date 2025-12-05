(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Corelib Require Import PosDef IntDef NatDef ring_checker.

Set Implicit Arguments.

(** The field tactic is essentially a preprocessing step to the ring tactic
(see file ring_checker.v). *)

(** Definition of field expressions *)
Inductive FExpr {C} : Type :=
| FEO : FExpr
| FEI : FExpr
| FEc : C -> FExpr
| FEX : positive -> FExpr
| FEadd : FExpr -> FExpr -> FExpr
| FEsub : FExpr -> FExpr -> FExpr
| FEmul : FExpr -> FExpr -> FExpr
| FEopp : FExpr -> FExpr
| FEinv : FExpr -> FExpr
| FEdiv : FExpr -> FExpr -> FExpr
| FEpow : FExpr -> N -> FExpr.
Arguments FExpr : clear implicits.

Section FieldChecker.
Variables (C : Type) (cO cI : C) (cadd cmul csub : C -> C -> C) (copp : C -> C).
Variables (pow_pos : C -> positive -> C).
Variables (ceqb : C -> C -> bool) (cdiv : C -> C -> C * C).
(* only requirement on cdiv is:
[forall x y, let (q, r) := cdiv x y in x = y * q + r] *)

(** forall l e1 e2, PEeval l (NPEadd e1 e2) = PEeval l (PEadd e1 e2) *)
Definition NPEadd e1 e2 :=
  match e1, e2 with
  | PEc c1, PEc c2 => PEc (cadd c1 c2)
  | PEc c, _ => if ceqb c cO then e2 else PEadd e1 e2
  |  _, PEc c => if ceqb c cO then e1 else PEadd e1 e2
  | _, _ => PEadd e1 e2
  end.

(** forall l e1 e2, PEeval l (NPEsub e1 e2) = PEeval l (PEsub e1 e2) *)
Definition NPEsub e1 e2 :=
  match e1, e2 with
  | PEc c1, PEc c2 => PEc (csub c1 c2)
  | PEc c, _ => if ceqb c cO then PEopp e2 else PEsub e1 e2
  |  _, PEc c => if ceqb c cO then e1 else PEsub e1 e2
  | _, _ => PEsub e1 e2
  end.

(** forall l e, PEeval l (NPEopp e) = PEeval l (PEopp e) *)
Definition NPEopp e := match e with PEc c => PEc (copp c) | _ => PEopp e end.

(** forall l e n, PEeval l (NPEpow e n) = PEeval l (PEpow e n) *)
Definition NPEpow x n :=
  match n with
  | N0 => PEc cI
  | Npos p =>
      if Pos.eqb p xH then x else
        match x with
        | PEc c =>
            if ceqb c cI then PEc cI else if ceqb c cO then PEc cO
            else PEc (pow_pos c p)
        | _ => PEpow x n
        end
  end.

(** forall l e1 e2, PEeval l (NPEmul e1 e2) = PEeval l (PEmul e1 e2) *)
Fixpoint NPEmul (x y : PExpr C) {struct x} : PExpr C :=
  match x, y with
  | PEc c1, PEc c2 => PEc (cmul c1 c2)
  | PEc c, _ => if ceqb c cI then y else if ceqb c cO then PEO else PEmul x y
  | _, PEc c => if ceqb c cI then x else if ceqb c cO then PEO else PEmul x y
  | PEpow e1 n1, PEpow e2 n2 =>
      if N.eqb n1 n2 then NPEpow (NPEmul e1 e2) n1 else PEmul x y
  | _, _ => PEmul x y
  end.

(** forall e1 e2, (e1 = e2) <-> (PExpr_eq e1 e2 = true) *)
Fixpoint PExpr_eq (e e' : PExpr C) {struct e} : bool :=
  match e, e' with
  | PEO, PEO | PEI, PEI => true
  | PEc c, PEc c' => ceqb c c'
  | PEX _ p, PEX _ p' => Pos.eqb p p'
  | PEadd e1 e2, PEadd e1' e2' => andb (PExpr_eq e1 e1') (PExpr_eq e2 e2')
  | PEsub e1 e2, PEsub e1' e2' => andb (PExpr_eq e1 e1') (PExpr_eq e2 e2')
  | PEmul e1 e2, PEmul e1' e2' => andb (PExpr_eq e1 e1') (PExpr_eq e2 e2')
  | PEopp e, PEopp e' => PExpr_eq e e'
  | PEpow e n, PEpow e' n' => andb (N.eqb n n') (PExpr_eq e e')
  | _, _ => false
  end.

(** forall l e1 p1 e2 p2 n e3, default_isIn e1 p1 e2 p2 = Some (n, e3) ->
(Pos.to_nat p1 > N.to_nat n
 /\ PEeval l (PEpow e2 (Npos p2))
    = PEeval l (PEmul (PEpow e1 (N.sub (Npos p1) n)) e3)) *)
Definition default_isIn e1 p1 e2 p2 :=
  if PExpr_eq e1 e2 then
    match Z.pos_sub p1 p2 with
    | Zpos p => Some (Npos p, PEc cI)
    | Z0 => Some (N0, PEc cI)
    | Zneg p => Some (N0, NPEpow e2 (Npos p))
    end
  else None.

(** forall l e1 p1 e2 p2 n e3, isIn e1 p1 e2 p2 = Some (n, e3) ->
(Pos.to_nat p1 > N.to_nat n
 /\ PEeval l (PEpow e2 (Npos p2))
    = PEeval l (PEmul (PEpow e1 (N.sub (Npos p1) n)) e3)) *)
Fixpoint isIn e1 p1 e2 p2 {struct e2}: option (N * PExpr C) :=
  match e2 with
  | PEmul e3 e4 =>
      match isIn e1 p1 e3 p2 with
      | Some (N0, e5) => Some (N0, NPEmul e5 (NPEpow e4 (Npos p2)))
      | Some (Npos p, e5) =>
          match isIn e1 p e4 p2 with
          | Some (n, e6) => Some (n, NPEmul e5 e6)
          | None => Some (Npos p, NPEmul e5 (NPEpow e4 (Npos p2)))
          end
      | None =>
          match isIn e1 p1 e4 p2 with
          | Some (n, e5) => Some (n, NPEmul (NPEpow e3 (Npos p2)) e5)
          | None => None
          end
      end
  | PEpow e3 N0 => None
  | PEpow e3 (Npos p3) => isIn e1 p1 e3 (Pos.mul p3 p2)
  | _ => default_isIn e1 p1 e2 p2
  end.

Record rsplit : Type := mk_rsplit {
  rsplit_left : PExpr C;
  rsplit_common : PExpr C;
  rsplit_right : PExpr C;
}.

(** forall l e1 p e2,
PEeval l (PEpow e1 (Npos p))
= PEeval l (PEmul (rsplit_left (split_aux e1 p e2))
              (rsplit_common (split_aux e1 p e2)))
/\ PEeval l e2
   = PEeval l (PEmul (rsplit_right (split_aux e1 p e2))
                 (rsplit_common (split_aux e1 p e2))) *)
Fixpoint split_aux e1 p e2 {struct e1} : rsplit :=
  match e1 with
  | PEmul e3 e4 =>
      let r1 := split_aux e3 p e2 in
      let r2 := split_aux e4 p (rsplit_right r1) in
      mk_rsplit (NPEmul (rsplit_left r1) (rsplit_left r2))
        (NPEmul (rsplit_common r1) (rsplit_common r2))
        (rsplit_right r2)
  | PEpow e3 N0 => mk_rsplit (PEc cI) (PEc cI) e2
  | PEpow e3 (Npos p3) => split_aux e3 (Pos.mul p3 p) e2
  | _ =>
      match isIn e1 p e2 xH with
      | Some (N0,e3) => mk_rsplit (PEc cI) (NPEpow e1 (Npos p)) e3
      | Some (Npos q, e3) =>
          mk_rsplit (NPEpow e1 (Npos q)) (NPEpow e1 (Npos (Pos.sub p q))) e3
      | None => mk_rsplit (NPEpow e1 (Npos p)) (PEc cI) e2
      end
  end.

(**
* forall l e1 e2,
    PEeval l e1
    = PEeval l (PEmul (rsplit_left (split e1 e2))
                  (rsplit_common (split e1 e2)))
* forall l e1 e2,
    PEeval l e2
    = PEeval l (PEmul (rsplit_right (split e1 e2))
                  (rsplit_common (split e1 e2)))
* forall l e1 e2,
    PEeval l e1 != 0 -> PEeval l (rsplit_left (split e1 e2)) != 0
* forall l e1 e2,
    PEeval l e2 != 0 -> PEeval l (rsplit_right (split e1 e2)) != 0 *)
Definition split e1 e2 := split_aux e1 xH e2.

Record linear : Type := mk_linear {
  num : PExpr C;
  denum : PExpr C;
  condition : list (PExpr C);
}.

(** main normalisation function
* [forall l e, PCond l (condition (Fnorm e)) ->
     PEeval l (denum (Fnorm e)) != 0]
* [forall l e : PCond l (condition (Fnorm e)) ->
     FEeval l e = PEeval l (num (Fnorm e)) / PEeval l (denum (Fnorm e))] *)
Fixpoint Fnorm (e : FExpr C) : linear :=
  match e with
  | FEO => mk_linear (PEc cO) (PEc cI) nil
  | FEI => mk_linear (PEc cI) (PEc cI) nil
  | FEc c => mk_linear (PEc c) (PEc cI) nil
  | FEX x => mk_linear (PEX C x) (PEc cI) nil
  | FEadd e1 e2 =>
      let x := Fnorm e1 in
      let y := Fnorm e2 in
      let s := split (denum x) (denum y) in
      mk_linear
        (NPEadd (NPEmul (num x) (rsplit_right s))
           (NPEmul (num y) (rsplit_left s)))
        (NPEmul (rsplit_left s) (NPEmul (rsplit_right s) (rsplit_common s)))
        (condition x ++ condition y)
  | FEsub e1 e2 =>
      let x := Fnorm e1 in
      let y := Fnorm e2 in
      let s := split (denum x) (denum y) in
      mk_linear
        (NPEsub (NPEmul (num x) (rsplit_right s))
           (NPEmul (num y) (rsplit_left s)))
        (NPEmul (rsplit_left s) (NPEmul (rsplit_right s) (rsplit_common s)))
        (condition x ++ condition y)
  | FEmul e1 e2 =>
      let x := Fnorm e1 in
      let y := Fnorm e2 in
      let s1 := split (num x) (denum y) in
      let s2 := split (num y) (denum x) in
      mk_linear (NPEmul (rsplit_left s1) (rsplit_left s2))
        (NPEmul (rsplit_right s2) (rsplit_right s1))
        (condition x ++ condition y)
  | FEopp e1 =>
      let x := Fnorm e1 in
      mk_linear (NPEopp (num x)) (denum x) (condition x)
  | FEinv e1 =>
      let x := Fnorm e1 in
      mk_linear (denum x) (num x) (num x :: condition x)
  | FEdiv e1 e2 =>
      let x := Fnorm e1 in
      let y := Fnorm e2 in
      let s1 := split (num x) (num y) in
      let s2 := split (denum x) (denum y) in
      mk_linear (NPEmul (rsplit_left s1) (rsplit_right s2))
        (NPEmul (rsplit_left s2) (rsplit_right s1))
        (num y :: condition x ++ condition y)
  | FEpow e1 n =>
      let x := Fnorm e1 in
      mk_linear (NPEpow (num x) n) (NPEpow (denum x) n) (condition x)
  end.

#[local] Abbreviation mk_monpol_list := (mk_monpol_list
  cO cI cadd cmul csub copp ceqb cdiv).
#[local] Abbreviation Pol_of_PExpr := (Pol_of_PExpr
  cO cI cadd cmul csub copp ceqb).
#[local] Abbreviation norm_subst := (norm_subst
  cO cI cadd cmul csub copp ceqb cdiv).

(** Main function, when [field_checker] returns [Some lc], The equality
[FEeval l fe1 = FEeval l fe2] holds under the hypotheses given by [lc], that is:
[forall cond_norm (cond_normP : forall l el, PCond l (cond_norm el) ->
       PCond l el) n l lpe fe1 fe2 lc,
   PEeval_eqs l lpe ->
   field_checker cond_norm n lpe fe1 fe2 = Some lc ->
   PCond l lc ->
 FEeval l fe1 = FEeval l fe2]
[cond_norm] is used to normalise the resulting conditions,
see below for implementations. *)
Definition field_checker cond_norm n lpe fe1 fe2 : option (list (PExpr C)) :=
  let lmp := mk_monpol_list lpe in
  let ne1 := Fnorm fe1 in
  let ne2 := Fnorm fe2 in
  let res :=
    Peq ceqb
      (norm_subst n lmp (PEmul (num ne1) (denum ne2)))
      (norm_subst n lmp (PEmul (num ne2) (denum ne1))) in
  if res then Some (cond_norm (app (condition ne1) (condition ne2))) else None.

(* Some general simpifications of the condition: eliminate duplicates,
   split multiplications *)

(* eliminate duplicates (through normal forms comparison)
[forall l a el, PCond l (Fcons0 a el) -> PEeval l a != 0 /\ PCond l el] *)
Fixpoint Fcons0 (e : PExpr C) (l : list (PExpr C)) {struct l} :=
  match l with
  | nil => cons e nil
  | cons a l1 =>
      if Peq ceqb (Pol_of_PExpr e) (Pol_of_PExpr a) then l
      else cons a (Fcons0 e l1)
  end.

(* split factorized denominators
[forall l a el, PCond l (Fcons00 a el) -> PEeval l a != 0 /\ PCond l el] *)
Fixpoint Fcons00 (e : PExpr C) (l : list (PExpr C)) {struct e} :=
  match e with
  | PEmul e1 e2 => Fcons00 e1 (Fcons00 e2 l)
  | PEpow e1 _ => Fcons00 e1 l
  | _ => Fcons0 e l
  end.

(* An unsatisfiable condition: issued when a division by zero is detected *)
Definition absurd_PCond := cons (PEc cO) nil.

(* [forall l a el, PCond l (Fcons1 a el) -> PEeval l a != 0 /\ PCond l el] *)
Fixpoint Fcons1 (e : PExpr C) (l : list (PExpr C)) {struct e} :=
  match e with
  | PEmul e1 e2 => Fcons1 e1 (Fcons1 e2 l)
  | PEpow e _ => Fcons1 e l
  | PEopp e => if ceqb (copp cI) cO then absurd_PCond else Fcons1 e l
  | PEc c => if ceqb c cO then absurd_PCond else l
  | _ => Fcons0 e l
  end.

(* simplification [forall l e, PEeval l (PEsimp e) = PEeval l e] *)
Fixpoint PEsimp (e : PExpr C) : PExpr C :=
  match e with
  | PEadd e1 e2 => NPEadd (PEsimp e1) (PEsimp e2)
  | PEmul e1 e2 => NPEmul (PEsimp e1) (PEsimp e2)
  | PEsub e1 e2 => NPEsub (PEsimp e1) (PEsimp e2)
  | PEopp e1 => NPEopp (PEsimp e1)
  | PEpow e1 n1 => NPEpow (PEsimp e1) n1
  | _ => e
  end.

(** [forall l a el, PCond l (Fcons2 a el) -> PEeval l a != 0 /\ PCond l el] *)
Definition Fcons2 e l := Fcons1 (PEsimp e) l.

Section Fapp.
Variable Fcons : PExpr C -> list (PExpr C) -> list (PExpr C).
(** [forall l el el',
  (forall l e el, PCond l (Fcons e el) -> PEeval l e != 0 /\ PCond l el) ->
PCond l (Fapp Fcons el el') -> PCond l el /\ PCond l el'] *)
Fixpoint Fapp (l m : list (PExpr C)) {struct l} : list (PExpr C) :=
  match l with nil => m | cons a l1 => Fcons a (Fapp l1 m) end.
End Fapp.

(** [forall Fcons l el,
  (forall l e el, PCond l (Fcons e el) -> PEeval l e != 0 /\ PCond l el) ->
PCond l (cond_norm Fcons el) -> PCond l el] *)
Definition cond_norm Fcons l := Fapp Fcons l nil.

End FieldChecker.
