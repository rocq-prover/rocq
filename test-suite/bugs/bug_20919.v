Goal forall n: nat, True.
  intros n.
  let x := n in
  clear x;
  assert_fails clearbody x.
Abort.
