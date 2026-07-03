(* -*- mode: coq; coq-prog-args: () -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 53 lines to 54 lines, then from 68 lines to 2005 lines, then from 2007 lines to 73 lines, then from 87 lines to 247 lines, then from 254 lines to 102 lines, then from 116 lines to 528 lines, then from 531 lines to 103 lines, then from 118 lines to 105 lines, then from 120 lines to 87 lines, then from 102 lines to 87 lines, then from 0 lines to 87 lines *)
(* coqc version 9.2+rc2 compiled with OCaml 4.14.2
   coqtop version 9.2+rc2
   Expected coqc runtime on this file: 0.000 sec
   Expected coqc peak memory usage on this file: 0.0 kb *)

Axiom proof_irrelevance : forall (P : Prop), forall x y : P, x = y.

Global Set Definitional UIP.
Module Export IsomorphismDefinitions.
#[export]
Set Universe Polymorphism.
Inductive eq@{s;u} {α:Type@{s;u}} (a:α) : α -> SProp
  := eq_refl : eq a a.

#[local] Notation "x = y" := (eq x y) : type_scope.
#[export]
Set Implicit Arguments.

Record Iso@{s s';u u'} (A : Type@{s;u}) (B : Type@{s';u'}) := {
    to :> A -> B;
    from : B -> A;
    to_from : forall x, to (from x) = x;
    from_to : forall x, from (to x) = x;
}.
#[local] Set Primitive Projections.
Record > rel_iso@{s s';u u'} {A B} (i : Iso@{s s';u u'} A B) (x : A) (y : B) : SProp := { proj_rel_iso :> i.(to) x = y }.

Existing Class Iso.

End IsomorphismDefinitions.

Variant SInhabited (A : Prop) : SProp := sinhabits : A -> SInhabited A.
Axiom sinhabitant@{} : forall {A : Prop}, SInhabited A -> A.

Module Import IsoEq.
#[local] Notation "x = y" := (IsomorphismDefinitions.eq x y) : type_scope.
Theorem f_equal@{s s';u u'} {A : Type@{s;u}} {B : Type@{s';u'}} (f : A -> B) {x y : A} (H : x = y) : f x = f y.
Admitted.
Lemma seq_of_peq_t@{u} {A : Prop} {x y : A} (H : Logic.eq x y) : IsomorphismDefinitions.eq@{Type;u} x y.
Admitted.

End IsoEq.
Module Export Imported.
#[local] Unset Implicit Arguments.
Inductive Eq@{s;u} (A : Type@{s;u}) (a : A) : A -> SProp :=
| Eq_refl : Eq A a a.
End Imported.
Monomorphic Definition imported_Corelib__Init__Logic__eq : forall x : Type, x -> x -> SProp.
exact ((@Imported.Eq)).
Defined.
Monomorphic Instance Corelib__Init__Logic__eq_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib__Init__Logic__eq x4 x6).
Proof.
  intros x1 x2 hx x3 x4 [H1] x5 x6 [H2].
  destruct H1.
destruct H2.
  unshelve refine {| to := _; from := _; to_from := _; from_to := _ |}.
  -
 intro H.
destruct H.
exact (Imported.Eq_refl _ _).
  -
 intro H.
apply sinhabitant.
    refine (match H in Imported.Eq _ _ z return
              forall y, IsomorphismDefinitions.eq (hx.(to) y) z -> SInhabited (x3 = y) with
            | Imported.Eq_refl _ _ => _ end x5 _).
    +
 intros y Hy.
      pose proof (f_equal hx.(from) Hy) as Hy2.
      pose proof (hx.(from_to) x3) as E1.
      pose proof (hx.(from_to) y) as E2.
      constructor.
      revert E1 E2 Hy2.
generalize (hx.(from) (hx.(to) x3)) (hx.(from) (hx.(to) y)).
      intros a b Ea Eb Eab.
destruct Ea.
destruct Eb.
destruct Eab.
reflexivity.
    +
 reflexivity.
  -
 cbv beta.
intro x.
reflexivity.
  -
 cbv beta.
intro x.
exact (IsoEq.seq_of_peq_t (proof_irrelevance _ _ _)).
Qed.
(* Used to look up a rel outside of the environment *)
