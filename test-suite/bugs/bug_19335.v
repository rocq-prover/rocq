Require Import Corelib.Classes.Morphisms.
Require Import Setoid.

Lemma fail A (R R' : relation A) :
  (eq ==> iff)%signature (Acc R) (Acc R') ->
  (forall a : A, Acc R a) <-> (forall a : A, Acc R' a).
Proof.
  intro H.
  Fail setoid_rewrite H.
Abort.

#[local] Instance all_eq_iff A : Proper ((@eq A ==> iff) ==> iff) (@all A).
Proof.
intros P Q H; split; intros HP x; apply (H x x eq_refl), HP.
Qed.

Lemma succeed A (R R' : relation A) :
  (eq ==> iff)%signature (Acc R) (Acc R') ->
  (forall a : A, Acc R a) <-> (forall a : A, Acc R' a).
Proof.
  intro H.
  setoid_rewrite H.
  match goal with |- (forall x : A, Acc R' x) <-> _ => reflexivity end.
Qed.
