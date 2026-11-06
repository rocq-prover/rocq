Goal nat -> True.
Proof.
  let f := open_constr:(fun n : nat => ?[v]) in
  intro k;
  let v0 := eval cbv in (f k) in
  let v1 := eval cbv in (f v0) in
  assert (v1 = 0) as H by admit;
  assert (k = 0).
  - rewrite H.
    reflexivity.
  - exact I.
Abort.

Goal nat -> True.
Proof.
  let f := open_constr:(fun n : nat => ?[v]) in
  intro k;
  let v0 := eval cbv in (f k) in
  let v1 := eval cbv in (f v0) in
  assert (v1 = k) by reflexivity.
  exact I.
Qed.

Goal nat -> nat -> nat -> True.
Proof.
  let f := open_constr:(fun n m : nat => ?[v]) in
  intros k a b;
  let v0 := eval cbv in (f k b) in
  let v1 := eval cbv in (f a v0) in
  assert (v1 = k).
  - Fail reflexivity.
Abort.
