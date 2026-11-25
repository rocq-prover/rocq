Goal True.
Proof.
pose (x := 0).
Succeed fold x in *.
Fail fold x in x.
Succeed change 0 with x in *.
Fail change 0 with x in x.
Succeed pattern x in *.
Fail pattern x in x.
Abort.
