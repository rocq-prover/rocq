(* The unifier must not refresh the algebraic sorts of an evar instance in positions which are
   not known to be covariant or contravariant. Here [apply path_arrow] solves [?B :=
   Type@{max(u,v)}] with CONV, in the type argument of an equality: refreshed to [Type@{w}]
   with only [max(u, v) <= w], the term is ill-typed unless the minimization guesses [w :=
   max(u, v)], which it does not when [w] occurs invariantly in the folded [univ_path@{w}]
   (from HoTT's [Book_2_17_ii_sigma]). *)

Set Universe Polymorphism.

Cumulative Inductive paths@{i} {A : Type@{i}} (a : A) : A -> Type@{i} :=
  idpath : paths a a.
Arguments idpath {A a}.

(* Non-dependent, as in HoTT: [?B := Type@{max(u,v)}] is an arity solved with CONV *)
Axiom path_arrow@{a b} : forall {A : Type@{a}} {B : Type@{b}} (f g : A -> B),
  (forall x, paths (f x) (g x)) -> paths f g.

Axiom ua@{k} : forall (X Y : Type@{k}), (X -> Y) -> (Y -> X) -> paths X Y.

(* A definition, as HoTT's [path_universe_uncurried]: [k] is invariant in its type *)
Definition univ_path@{k} (X Y : Type@{k}) (f : X -> Y) (g : Y -> X) : paths X Y := ua X Y f g.

Section S.
  Universes a u v.
  Context {A : Type@{a}} (B : A -> Type@{u}) (C : A -> Type@{v})
    (f : forall x, B x -> C x) (g : forall x, C x -> B x).

  (* The equality is at [A -> Type@{max(u,v)}] *)
  Definition fibr (q : paths B C) : paths B C := q.

  Definition fibr_proof : paths B C.
  Proof.
    apply fibr.
    apply path_arrow; intro x.
    apply univ_path.
    - apply f.
    - apply g.
  Defined.
End S.
