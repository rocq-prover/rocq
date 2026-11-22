(* The sort of an arity binder is contravariant for typing: a universe occurring only there is
   raised to its upper bound, as for [B] in HoTT's [path_universe_uncurried] (without
   [Universe Minimization Compat]). The declaration accepts the same applications, with one
   universe fewer. *)

Set Universe Polymorphism.

Cumulative Inductive paths@{i} {A : Type@{i}} (a : A) : A -> Type@{i} :=
  idpath : paths a a.

Axiom ua@{k} : forall (X Y : Type@{k}), (X -> Y) -> paths X Y.

(* [B : Type@{v}] with [v <= u] only: [v := u] *)
Definition pu {A B : Type} (f : A -> B) : paths A B := ua A B f.
Check pu@{_}.

(* Arguments in different universes are still accepted *)
Check fun (A : Type@{Set+1}) (B : Type@{Set}) (f : A -> B) => pu f.

(* The conclusion of a family: [P : A -> Type@{v}] and [Q : Type@{w}] share their universe *)
Definition pf {A : Type} (P : A -> Type) (Q : Type) (f : forall a, P a -> Q) (a : A)
  : paths (P a) Q := ua _ _ (f a).
Check pf@{_ _}.
