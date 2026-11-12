(* A universe of the type of a binder (a hypothesis, an assumption, the binder of a definition),
   relevant for cumulativity but not for the sort of this type, is not set to its upper bound,
   nor to Set without Universe Minimization ToSet: it is part of the type of the declaration *)
Set Universe Polymorphism.
Set Printing Universes.
Unset Universe Minimization ToSet.
NonCumulative Record WrapI@{u} (A : Type@{u}) : Type@{u} := wrapI { unwrapI : A }.

Section S.
  Universes p q.
  Variable P : Type@{p} -> Type@{q}.
  Hypothesis H : P (WrapI nat).
  (* Was [P (WrapI@{p} nat)] *)
  Definition hyp := H.
End S.
About hyp.

Section S'.
  Universes p q.
  Variable P : Type@{p} -> Type@{q}.
  (* Was [P (WrapI@{p} nat)] *)
  Definition binder (H : P (WrapI nat)) := H.
End S'.
About binder.

(* Was [P (WrapI@{u} nat)] with [u] the universe of the domain of [P] *)
Axiom ax : forall (P : Type -> Type), P (WrapI nat).
About ax.

(* With Universe Minimization ToSet, the universe is set to Set *)
Set Universe Minimization ToSet.
Section T.
  Universes p q.
  Variable P : Type@{p} -> Type@{q}.
  Hypothesis H : P (WrapI nat).
  Definition hyp_set := H.
End T.
About hyp_set.
