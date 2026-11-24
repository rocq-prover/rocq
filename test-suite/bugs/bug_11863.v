Notation "" := id (only printing).
Fail Notation "" := id.

Notation "a +++ b" := (a + b) (only printing, at level 50, left associativity).
Notation "a +++ b" := (a - b).
Check 1 +++ 2.

Notation "%" := 0 (only printing).
Notation "%" := 0 (only parsing).
Check %.
