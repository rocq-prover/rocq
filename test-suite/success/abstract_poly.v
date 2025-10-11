Set Universe Polymorphism.

Inductive path@{i} {A : Type@{i}} (x : A) : A -> Type@{i} := refl : path x x.
Inductive unit@{i} : Type@{i} := tt.

Instance path_Has_Leibniz_elim@{l l' l''} : Has_Leibniz@{Type Type Type;l l' l''} (@path) :=
  fun A x P t y e => match e with refl _ => t end.

Lemma foo@{i j} : forall (m n : unit@{i}) (P : unit -> Type@{j}), path m n -> P m -> P n.
Proof.
intros m n P e p.
abstract (rewrite e in p; exact p).
Defined.

Check foo_subproof@{Set Set}.

Lemma bar : forall (m n : unit) (P : unit -> Type), path m n -> P m -> P n.
Proof.
intros m n P e p.
abstract (rewrite e in p; exact p).
Defined.

Check bar_subproof@{Set Set}.
