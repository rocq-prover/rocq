Fail Check fun (y : nat -> nat) =>
  (fun (e : nat) (f : (fun _ => nat) e) (H : e = y f) => tt) _ _ eq_refl.
