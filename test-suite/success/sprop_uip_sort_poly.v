
Set Definitional UIP.
Set Universe Polymorphism.

Inductive seq@{s;i} {A:Type@{s;i}} (a:A) : A -> SProp :=
  srefl : seq a a.

Definition transport@{s s'; i j} (A:Type@{s;i}) (P:A -> Type@{s';j}) {x y} (e:seq x y) (v:P x) : P y :=
  match e with srefl _ => v end.

Lemma test@{s s'; i j} (A:Type@{s;i}) (P:A -> Type@{s';j}) x t (e:seq x x) : seq (transport A P e t) t.
Proof.
  reflexivity.
Defined.
