Set Warnings "-notation-incompatible-level".
Reserved Notation "x == y" (at level 70, y at next level, only printing).
Notation "x == y" := (x = y) (at level 17, y at next level).
Check (0 == (1 + 1)).
Fail Check (0 == 1 + 1).
