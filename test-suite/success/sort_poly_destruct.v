Set Universe Polymorphism.

Inductive sum@{sl sr s|ul ur|} (A : Type@{sl|ul}) (B : Type@{sr|ur}) : Type@{s|max(ul,ur)} :=
| inl : A -> sum A B
| inr : B -> sum A B.
Arguments inl {_} {_} _.
Arguments inr {_} {_} _.

Inductive sig@{s s' s''|u v|} (A : Type@{s|u}) (P : A -> Type@{s'|v}) : Type@{s''|max(u,v)} :=
  | existsS : forall x, P x -> sig A P.
Arguments existsS {_} {_} _ _.

Set Printing Universes.

Lemma testElim@{s s'|u v|s ~> s'} :
  forall (A B : Prop) (P : sum@{Prop Prop s|Set Set} A B -> Type@{s'|Set})
    (Q : sum@{Prop Prop s'|Set Set} A B -> Type@{s'|Set}) (x : sum@{Prop Prop s|Set Set} A B),
    P x -> sig (sum@{Prop Prop s'|Set Set} A B) Q.
Proof.
  intros ????? HP.
  refine (existsS (match x return sum@{Prop Prop s'|Set Set} A B with
                   | inl x => inl x
                   | inr y => inr y
                   end) _).

  destruct x. Abort.
