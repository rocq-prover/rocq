Set Universe Polymorphism.

Inductive sum@{sl sr s;ul ur|} (A : Univ@{sl;ul}) (B : Univ@{sr;ur}) : Univ@{s;max(ul,ur)} :=
| inl : A -> sum A B
| inr : B -> sum A B.
Arguments inl {_} {_} _.
Arguments inr {_} {_} _.

Inductive sig@{s s' s'';u v|} (A : Univ@{s;u}) (P : A -> Univ@{s';v}) : Univ@{s'';max(u,v)} :=
  | existsS : forall x, P x -> sig A P.
Arguments existsS {_} {_} _ _.

Set Printing Universes.

Lemma testElim@{s s';u v|s -> s'} :
  forall (A B : Prop) (P : sum@{Prop Prop s;0 0} A B -> Univ@{s';0})
    (Q : sum@{Prop Prop s';0 0} A B -> Univ@{s';0}) (x : sum@{Prop Prop s;0 0} A B),
    P x -> sig (sum@{Prop Prop s';0 0} A B) Q.
Proof.
  intros ????? HP.
  refine (existsS (match x return sum@{Prop Prop s';0 0} A B with
                   | inl x => inl x
                   | inr y => inr y
                   end) _).

  destruct x. Abort.
