Module M.
  Sort s.
  Fail Sort s.
End M.
Module N.
  Sort s.
End N.
Sort s.

Check fun A:Type@{M.s;Set} => A:Type@{M.s;Set}.
Fail Check fun A:Type@{M.s;Set} => A:Type@{N.s;Set}.
