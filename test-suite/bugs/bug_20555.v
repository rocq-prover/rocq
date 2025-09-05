Fail
Fixpoint error (t : unit) {struct t} : False :=
  (fix rec (n : nat) {struct n} :=
    match n with 0 => error | S n => rec n end)
    1 t.
