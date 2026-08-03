#[projections(primitive)]
Record sigma {A} {B : A -> Set} := mksigma { fst : A ; snd : B fst }.

Definition T (b : bool) := if b then nat else False.

Definition test (n : nat) : n = n :=
  match @mksigma _ T true n with mksigma _ _ a b => (eq_refl : b = n) end.
