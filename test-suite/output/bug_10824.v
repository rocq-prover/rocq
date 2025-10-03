Module A.
Abbreviation F := False.
Notation "!!" := False (at level 0).
Check False.
End A.

Module B.
Notation "!!" := False (at level 0).
Abbreviation F := False.
Notation "!!" := False (at level 0).
Check False.
End B.
