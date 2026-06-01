Section S.
Variable a:nat.
Definition b:=a.
Goal b=b.
Proof.
  Fail rename a into c.
  generalize b. intros b.
  rename a into c.
  Fail unfold b.
Abort.
End S.
