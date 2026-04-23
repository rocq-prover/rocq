Set Primitive Projections.

Inductive eq (A : Type) (a : A) : forall _ : A, Prop :=
  eq_refl : eq A a a.

(* ================================================================ *)
(* Baseline: records with SProp fields in relevant sorts have NoEta *)
(* ================================================================ *)

Record RPropToSProp (A : SProp) : Prop := { rprop_field : A }.

Fail Definition rprop_eta (A : SProp) (r : RPropToSProp A)
  : eq _ r (Build_RPropToSProp A (rprop_field A r)) := eq_refl _ r.

Record RTypeToSProp (A : SProp) : Type := { rtype_field : A }.

Fail Definition rtype_eta (A : SProp) (r : RTypeToSProp A)
  : eq _ r (Build_RTypeToSProp A (rtype_field A r)) := eq_refl _ r.

(* ================================================================ *)
(* With Unset Elimination Checking: these records now get eta       *)
(* ================================================================ *)

Unset Elimination Checking.

Record RPropToSPropEta (A : SProp) : Prop := { rprop_eta_field : A }.

Definition rprop_eta_ok (A : SProp) (r : RPropToSPropEta A)
  : eq _ r (Build_RPropToSPropEta A (rprop_eta_field A r)) := eq_refl _ r.

Record RTypeToSPropEta (A : SProp) : Type := { rtype_eta_field : A }.

Definition rtype_eta_ok (A : SProp) (r : RTypeToSPropEta A)
  : eq _ r (Build_RTypeToSPropEta A (rtype_eta_field A r)) := eq_refl _ r.

(* Multiple SProp fields *)

Record RPair (A B : SProp) : Prop := { rfst : A; rsnd : B }.

Definition rpair_eta (A B : SProp) (r : RPair A B)
  : eq _ r (Build_RPair A B (rfst A B r) (rsnd A B r)) := eq_refl _ r.

(* Eta expands both sides, and SProp fields are irrelevant, so x = y *)

Record RWrap (A : SProp) : Prop := { unwrap : A }.

Definition rwrap_eta (A : SProp) (x : RWrap A)
  : eq _ x (Build_RWrap A (unwrap A x)) := eq_refl _ x.

Set Elimination Checking.

(* ================================================================ *)
(* Records with relevant fields already have eta, no flag needed    *)
(* ================================================================ *)

Inductive unit : Type := tt.

Record RRelevant := { rrel_field : unit }.

Definition rrel_eta (r : RRelevant)
  : eq _ r (Build_RRelevant (rrel_field r)) := eq_refl _ r.

(* SProp records with SProp fields already have eta *)

Record RSPropToSProp (A : SProp) : SProp := { rsprop_field : A }.

Inductive seq (A : SProp) (a : A) : forall _ : A, SProp :=
  seq_refl : seq A a a.

Definition rsprop_eta (A : SProp) (r : RSPropToSProp A)
  : seq _ r (Build_RSPropToSProp A (rsprop_field A r)) := seq_refl _ r.

(* ================================================================ *)
(* Rocq version of the Lean Inhabited' example                      *)
(*                                                                  *)
(* In Lean:                                                         *)
(*   universe u                                                     *)
(*   class Inhabited' (α : Sort u) where default : α               *)
(*   axiom MyProp : Prop                                            *)
(*   axiom mp : MyProp                                              *)
(*   def h : Inhabited' MyProp := Inhabited'.mk mp                  *)
(*   def test : MyProp := h.default                                 *)
(*   theorem Inhabited'.eta α (x : Inhabited' α) :                  *)
(*     Inhabited'.mk x.default = x := by rfl                        *)
(*   axiom h2 : Inhabited' MyProp                                   *)
(*   def test_eta := Inhabited'.eta MyProp h2                        *)
(*                                                                  *)
(* With a Prop field (relevant in Rocq), eta already works.          *)
(* ================================================================ *)

Record Inhabited' (A : Prop) : Type :=
  mk_Inhabited' { default' : A }.

Axiom MyProp : Prop.
Axiom mp : MyProp.

Definition h : Inhabited' MyProp := mk_Inhabited' MyProp mp.
Definition test : MyProp := default' MyProp h.

Definition Inhabited'_eta (A : Prop) (x : Inhabited' A)
  : eq _ (mk_Inhabited' A (default' A x)) x := eq_refl _ x.

Axiom h2 : Inhabited' MyProp.
Definition test_eta := Inhabited'_eta MyProp h2.

(* With SProp field: needs Unset Elimination Checking for eta *)

Unset Elimination Checking.

Record Inhabited'S (A : SProp) : Type :=
  mk_Inhabited'S { defaultS : A }.

Axiom MySProp : SProp.
Axiom msp : MySProp.

Definition hS : Inhabited'S MySProp := mk_Inhabited'S MySProp msp.
Definition testS : MySProp := defaultS MySProp hS.

Definition Inhabited'S_eta (A : SProp) (x : Inhabited'S A)
  : eq _ (mk_Inhabited'S A (defaultS A x)) x := eq_refl _ x.

Axiom h2S : Inhabited'S MySProp.
Definition test_etaS := Inhabited'S_eta MySProp h2S.

Set Elimination Checking.

(* Without the flag, the SProp version fails *)

Record Inhabited'S_noeta (A : SProp) : Type :=
  mk_Inhabited'S_noeta { defaultS_noeta : A }.

Fail Definition noeta_fail (A : SProp) (x : Inhabited'S_noeta A)
  : eq _ (mk_Inhabited'S_noeta A (defaultS_noeta A x)) x := eq_refl _ x.

(* ================================================================ *)
(* ================================================================ *)
(* Fixpoints on records with eta are rejected                       *)
(* ================================================================ *)

Unset Elimination Checking.

Record RBoxProp (A : Prop) : Prop := { unbox_prop : A }.

Fail Definition bad := fix f (x : RBoxProp True) : True := unbox_prop True x.

Set Elimination Checking.
