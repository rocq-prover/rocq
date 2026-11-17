Goal forall y : nat, True.
Proof.
intros y.
eassert (F : ?[n] = ?[n] :> nat) by reflexivity; clear F.
eassert (H : True) by abstract (
  eassert (D : ?[d] = ?[d] :> nat) by reflexivity;
  assert (W : ?d@{y := 0} = ?d@{y := 0}) by reflexivity;
  let _ := open_constr:(_ : nat) in
  instantiate (d := ?n); instantiate (n := y); exact I).
Abort.
