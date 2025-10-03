
Set Universe Polymorphism.

Cumulative Inductive EQ {A} (x : A) : A -> Type
  := EQ_refl : EQ x x.

Lemma renamed_EQ_rect {A} (x:A) (P : A -> Type)
  (c : P x) (y : A) (e : EQ x y) : P y.
Proof. destruct e. assumption. Qed.

Lemma renamed_EQ_rect_r {A} (x:A) (P : A -> Type)
  (c : P x) (y : A) (e : EQ y x) : P y.
Proof. destruct e. assumption. Qed.

(* rewriting is now based on typeclasses defined in Corelib.Init.Equality.v *)

Definition rename_EQ_Leibniz_elim : Has_Leibniz (@EQ)
  := @renamed_EQ_rect.
Hint Resolve rename_EQ_Leibniz_elim : rewrite_instances.

Definition rename_EQ_Leibniz_r_elim : Has_Leibniz_r (@EQ)
  := @renamed_EQ_rect_r.
Hint Resolve rename_EQ_Leibniz_r_elim : rewrite_instances.

Lemma EQ_sym1 {A} {x y : A} (e : EQ x y) : EQ y x.
Proof. rewrite e. reflexivity. Qed.

Lemma EQ_sym2 {A} {x y : A} (e : EQ x y) : EQ y x.
Proof.
  rewrite <- e.
  reflexivity.
Qed.

Require Import ssreflect.

Lemma ssr_EQ_sym1 {A} {x y : A} (e : EQ x y) : EQ y x.
Proof. rewrite e. reflexivity. Qed.

Lemma ssr_EQ_sym2 {A} {x y : A} (e : EQ x y) : EQ y x.
Proof. rewrite -e. reflexivity. Qed.
