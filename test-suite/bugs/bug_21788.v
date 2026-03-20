Inductive sTrue : SProp := stt.
Set Primitive Projections.

Inductive baz := { p : baz }.
Goal forall x, x = {| p := x.(p) |}.
Proof.
  intros x.
  Fail destruct x.
Abort.

Record foo := { bar : sTrue }.
Goal forall x y : foo, x = y.
Proof.
  intros x y.
  Fail destruct x, y.
Abort.
