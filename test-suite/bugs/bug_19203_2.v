Set Universe Polymorphism.

Inductive eq@{s s';u|} {A:Univ@{s;u}} (a:A) : A -> Univ@{s';Set} := refl : eq a a.

Register eq as core.eq.type.
Register refl as core.eq.refl.

Goal True.
  remember 0 as x.
  let _ := constr:(Heqx : _ : SProp) in idtac.
  exact I.
Qed.
