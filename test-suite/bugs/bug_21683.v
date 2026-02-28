Fail Fixpoint F (n : nat) : False :=
  (fix G F (n : nat) {struct n} : False := F n) F n.
