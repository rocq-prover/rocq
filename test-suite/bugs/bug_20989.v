From Corelib Require Import Extraction.

Extraction Language Haskell.

Module Type S.
Definition n := 0.
End S.

Module A.
Definition n := 0.
End A.

Module M (X : S).
Module In := X.
Definition n := In.n.
End M.

Module N := M(A).

Recursive Extraction N.
