Inductive vec : nat -> Type := vnil : vec 0 | vcons : forall n, vec n -> vec (S n).

Definition g (b : bool) := if b then 1 else 0.

Axiom foo : forall (X : Type) (g : X -> nat) (x : X) (v : vec (g x)) (n : nat), n = 0 -> True.

Goal True.
Proof.
  eapply foo with (x := true) (v := vcons _ vnil) (g := g).
  reflexivity.
Qed.

Axiom P : forall (X : Type), X -> Prop.
Axiom bar : forall (X : Type) (g : X -> nat) (y : X) (x : X) (v : vec (g x)) (n : nat), n = 0 -> P X y.

Goal P bool false.
Proof.
  eapply bar with (x := true) (v := vcons _ vnil) (g := g).
  reflexivity.
Qed.

Module CoercionOrder.

Axiom A B : Type.
Axiom a : A.
Axiom f : A -> B.
Coercion f : A >-> B.
Axiom l : list B.
Axiom foo : forall (X : Type) (F : Type -> Type) (x : X) (v : F X) (n : nat), n = 0 -> True.

Goal True.
Proof.
  eapply foo with (x := a) (v := l).
  reflexivity.
Qed.

End CoercionOrder.
