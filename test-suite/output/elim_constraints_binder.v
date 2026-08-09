(* Elimination constraints should show up when polymorphic binders are
   reported as incompatible, otherwise both sides of the message print
   the same thing. *)

Set Universe Polymorphism.

Module Type M.
  Parameter T@{s; u|Set < u} : unit.
End M.

Module Impl.
  Definition T@{s; u|s -> Type, Set < u} := tt.
End Impl.

Fail Module M2 : M := Impl.
