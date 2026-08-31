Set Universe Polymorphism.

Module Type M.
  Parameter T@{s; u|Set < u} : unit.
End M.

Module M2.
  Definition T@{s; u|s -> Type, Set < u} := tt.
End M2.

Fail Module M3 : M := M2.
