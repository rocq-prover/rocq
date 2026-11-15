From Corelib Require Import ssreflect.
Set Primitive Projections.

Record foo := Foo {
  foo_car : Type;
  foo_0 : foo_car;
}.

Arguments foo_car : simpl never.
Arguments foo_0 : simpl never.

Definition nat_foo := Foo nat 0.

Goal foo_0 nat_foo = 0.
Proof.
  rw /foo_0.
  simpl.
  match goal with |- 0 = 0 => reflexivity end.
Qed.

Record bar (A : Type) := Bar { b1 : A; b2 : A }.
Arguments b1 {A} : simpl never.
Arguments b2 {A} : simpl never.

Goal b1 (Bar _ 0 1) = b1 (Bar _ 2 3) /\ b2 (Bar _ 4 5) = 5.
Proof.
  rw {2}/b1; simpl.
  match goal with |- b1 _ = 2 /\ b2 _ = 5 => idtac end.
  rw [b2 _]/b2; simpl.
  match goal with |- b1 _ = 2 /\ 5 = 5 => idtac end.
  Fail rw {2}/b1.
  rw /b1; simpl.
  match goal with |- 0 = 2 /\ 5 = 5 => idtac end.
Abort.
