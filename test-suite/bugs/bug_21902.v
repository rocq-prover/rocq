(* Check that with Module clauses perform the correct equality check for nested modules *)

Module Type Inner.
  Parameter t : Type.
End Inner.

Module ConcreteInner : Inner.
  Definition t := True.
End ConcreteInner.

Module ConcreteInner2 : Inner.
  Definition t := False.
End ConcreteInner2.

Module Wrapper.
  Module Sub := ConcreteInner.
End Wrapper.

Module Type MT.
  Module A := Wrapper.
End MT.

(* This should fail because A.Sub = Wrapper.Sub = ConcreteInner != ConcreteInner2 *)
Fail Module Type Bad := MT with Module A.Sub := ConcreteInner2.

(* But this should succeed. *)
Module Type Good := MT with Module A.Sub := ConcreteInner.
