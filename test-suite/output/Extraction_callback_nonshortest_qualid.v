From Corelib Require Extraction.

Extraction Language OCaml.

Module A.
  Definition f (n : nat) := S n.
End A.

Import A.

Extract Callback A.f.
Extraction A.f.
Extraction TestCompile A.f.
