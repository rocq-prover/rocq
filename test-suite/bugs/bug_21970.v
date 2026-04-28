Set Universe Polymorphism.
Definition X@{u} := tt.
Inductive bla@{u} : Set := C (x : unit := X@{u}).

Definition bli@{a b}
  := eq_refl : match C@{b} with C x => x end = tt.

(* Error: Anomaly "Uncaught exception Invalid_argument("index out of bounds")." *)
