Module Import A.
Module B.
Notation x := tt.
Notation "1" := unit.
End B.
End A.
Check B.x. (* should say tt *)
