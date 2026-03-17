(* Test sort cumulativity for polymorphic inductive types *)

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Polymorphic Inductive Sort Cumulativity.

(* A sort-polymorphic isomorphism record *)
Record Iso@{s s'; u u'} (A : Type@{s; u}) (B : Type@{s'; u'}) : Type@{s; u} := {
  iso_fun : A -> B ;
  iso_inv : B -> A
}.

(* Test 1: Prop and Type are in the same connected component *)
(* Prop -> Type in first sort position should succeed *)
Axiom prop_iso : Iso@{Prop Prop; Set Set} True True.
Check (prop_iso : Iso@{Type Prop; Set Set} True True).

(* Test 2: Type -> Prop should also work (connected component, not ordering) *)
Axiom type_iso : Iso@{Type Prop; Set Set} True True.
Check (type_iso : Iso@{Prop Prop; Set Set} True True).

(* Test 3: SProp is alone in its own connected component - SProp <-> Prop should fail *)
Fail Check (prop_iso : Iso@{SProp Prop; Set Set} True True).

(* Test 4: Without sort cumulativity, Prop -> Type should fail *)
Unset Polymorphic Inductive Sort Cumulativity.
Record Iso2@{s s'; u u'} (A : Type@{s; u}) (B : Type@{s'; u'}) : Type@{s; u} := {
  iso2_fun : A -> B ;
  iso2_inv : B -> A
}.
Axiom prop_iso2 : Iso2@{Prop Prop; Set Set} True True.
Fail Check (prop_iso2 : Iso2@{Type Prop; Set Set} True True).
