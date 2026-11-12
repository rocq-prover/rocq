Set Primitive Projections.

Record prod A B := pair { fst : A ; snd : B }.
Scheme Equality for prod.

Check prod_eq_dec : forall A B (eq_A : A -> A -> bool) (eq_B : B -> B -> bool),
  (forall x y : A, eq_A x y = true -> x = y) ->
  (forall x y : B, eq_B x y = true -> x = y) ->
  (forall x y : A, x = y -> eq_A x y = true) ->
  (forall x y : B, x = y -> eq_B x y = true) ->
  forall x y : prod A B, {x = y} + {x <> y}.

Unset Primitive Projections.
Inductive foo A := Foo : prod A A -> foo A | Bar.
Scheme Equality for foo.

Set Primitive Projections.
Record bar A B := { b1 : prod A B; b2 : foo A }.
Scheme Equality for bar.
