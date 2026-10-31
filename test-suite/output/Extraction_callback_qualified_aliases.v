From Corelib Require Extraction.

Extraction Language OCaml.

Module A.
  Definition f (n : nat) := S n.
End A.

Module B.
  Definition f (n : nat) := n.
End B.

Extract Callback A.f.
Extract Callback B.f.

Extraction A.f.
Extraction B.f.
Extraction TestCompile A.f B.f.
