Class C := { tag : nat }.

Module A.
#[export] Instance a : C := {| tag := 1 |}.
End A.

Module B.
#[export] Instance b : C := {| tag := 2 |}.
End B.

Import A.
Import B.
(* Dubious behaviour: loading an existing hint again does not refresh its insertion order currently, but
   it probably should. *)
Import A.

Definition chosen : C := ltac:(typeclasses eauto).
Example newer_instance_keeps_priority : @tag chosen = 2 := eq_refl.
(* Replace 2 with 1 above when fixing the semantics *)
