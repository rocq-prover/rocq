Axiom Z : Set.
Class ops (T:Type).
Definition Zops:@ops Z. Admitted.

Module A.
  #[global] (* changing this global to export makes the second pose succeed *)
  Existing Instance Zops.
  #[export]
  Existing Instance Zops.
End A.

Module Import B.
  #[export] Instance Tops T: @ops T := {}.
End B.

Fail Type _ : ops _.
(* picked Tops which leaves an unsolved evar for T *)

Import A.

Type _ : ops _.
(* picked Zops *)

Remove Hints Zops : typeclass_instances.

Fail Type _ : ops _.
(* picked Tops *)

Import A.
(* was bugged: import incorrectly thought zops was still a hint
   so didn't add it again *)

Type _ : ops _.
(* should pick Zops *)
