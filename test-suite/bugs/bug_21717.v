Module M.
  Sort s.
  Fail Sort s.
End M.
Module N.
  Sort s.
End N.
Sort s.

Check fun A:Univ@{M.s;Set} => A:Univ@{M.s;Set}.
Fail Check fun A:Univ@{M.s;Set} => A:Univ@{N.s;Set}.
