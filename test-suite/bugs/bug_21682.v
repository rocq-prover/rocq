Fail Fixpoint F (n : nat) : nat :=
  match n with
  | O => O
  | S k =>
    (fix f (p : nat) (m : nat) {struct m} :=
       match m with O => p | S m' => g (S p) m' end
     with g (q : nat) (m : nat) {struct m} :=
       match m with O => F q | S m' => f q m' end
     for f) k k
  end.
