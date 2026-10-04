Module Type S. End S.

Module F (X : S).
  Module M : S.
    Module N. End N.
  End M.
End F.

Module Z. End Z.

Module R := F Z.
