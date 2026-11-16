Record lattice T := { carrier := T; top : carrier ; bottom : carrier }.
Scheme Equality for lattice.
Check lattice_eq_dec.

Set Primitive Projections.
Record plattice T := { pcarrier := T; ptop : pcarrier ; pbottom : pcarrier }.
Scheme Equality for plattice.

Record pr := { a : nat; c := 0; b : bool }.
Scheme Equality for pr.
Unset Primitive Projections.

Inductive foo (T : Type) :=
| C (n : nat) (k := S n) (U := T) (x : U) (v : nat) (y := k) (w : U)
| D (b : bool).
Scheme Equality for foo.
Check foo_eq_dec.

Inductive bar (T : Type) := E (k := 0) (j := 0) (x : T).
Goal forall T x y, E T x = E T y -> x = y.
Proof.
intros T x y H.
injection H.
intros Hxy.
exact Hxy.
Qed.
