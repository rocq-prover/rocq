Set Universe Polymorphism.

Inductive Acc@{s s';u v} {A : Type@{s;u}} (R : A -> A -> Prop) (x : A) : Type@{s';v} :=
| Acc_intro : (forall y : A, R y x -> Acc R y) -> Acc R x.

(* We should be able to define (with tactics) a fixpoint from [s'] to [Type] if [s' -> Prop]. *)
Fixpoint Acc_elim@{s s' ; u v w | s' -> Prop, u <= w}
  {A : Type@{s;u}} {R : A -> A -> Prop} {P : A -> Type@{w}}
  (f : forall x : A, (forall y : A, R y x -> Acc@{s s';u w} R y) -> (forall y : A, R y x -> P y) -> P x)
  (x : A) (a : Acc@{s s';u w} R x) {struct a} : P x.
Proof.
  refine (f x (fun y r => _) (fun y r => _)).
  - destruct a. now apply a.
  - unshelve eapply Acc_elim; eauto.
    destruct a. now apply a.
Defined.

Inductive sum@{sl sr s;ul ur|} (A : Type@{sl;ul}) (B : Type@{sr;ur}) : Type@{s;max(ul,ur)} :=
| inl : A -> sum A B
| inr : B -> sum A B.
Arguments inl {_ _} _.
Arguments inr {_ _} _.

(* Likewise but with an opaque proof. *)
Lemma test@{sl sr s;ul ur|s -> Prop} {A : Type@{sl;ul}} {B : Type@{sr;ur}}
  (u : sum@{sl sr s;ul ur} A B) : sum@{sl sr Prop;ul ur} A B.
Proof.
  destruct u.
  - exact (inl a).
  - exact (inr b).
Qed.
