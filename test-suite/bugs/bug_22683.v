Set Definitional UIP.

Inductive seq (x : nat) : nat -> SProp := srefl : seq x x.

Definition reduce_one_binder :=
  Eval lazy in
  fun (x y : nat) (e : seq x y) =>
    (fun (p : seq x y) =>
       match p in seq _ z return z = z with srefl _ => eq_refl end) e.
