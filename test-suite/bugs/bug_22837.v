Inductive foo (T : Type) := C (k := 0) (j := 0) (x : T).

Goal forall T x y, C T x = C T y -> x = y.
Proof.
intros T x y H.
injection H.
intros Hxy.
exact Hxy.
Qed.
