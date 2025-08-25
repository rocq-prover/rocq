Module A.
Abbreviation F := False.
Notation "!!" := False (at level 100).
Check False.
End A.

Module B.
Notation "!!" := False (at level 100).
Abbreviation F := False.
Notation "!!" := False (at level 100).
Check False.
End B.
