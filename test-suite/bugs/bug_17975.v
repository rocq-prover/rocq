Polymorphic Cumulative Record WType: Type := { getWType: Type; }.

Universe u.
Inductive Freer (E: WType -> Type) (R: WType@{u}): Type@{u} :=
  | Event {X: WType} (e: E X).

Definition id {E} {T: WType@{u}} (u: Freer E T) := u.

Parameter event: forall {E T}, E T -> Freer E T.
Fail Parameter trivial: forall {E: WType -> Type} {T} (e: E T),
  id (event e) = event e.
