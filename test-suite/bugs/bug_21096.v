#[projections(primitive)]
Record T := { a : Set }.

Goal forall x, x.(a) = x.(a).
  unfold a at 2. (* anomaly *)
Abort.
