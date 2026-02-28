Fixpoint iterate_to_neg (f : nat -> Type) (n : nat) (seed : nat) : Type :=
    match n with
    | O => f seed -> False
    | S m => iterate_to_neg f m seed
    end.

Fail Fixpoint russell (n : nat) : Type :=
    match n with
    | O => True
    | S m => iterate_to_neg russell 1 (S m)
    end.

Fail Fixpoint F (n : unit) : False :=
  (fix G F (n : unit) {struct n} : False := F tt) F n.
