#[universes(cumulative)]
Polymorphic Inductive eq@{s s';l +|} {A:Univ@{s;l}} (x:A) : A -> Univ@{s';_} :=
  eq_refl : eq x x.

Check eq 0 0 : SProp.
Check eq 0 0 : Prop.
