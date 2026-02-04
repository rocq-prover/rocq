Module Type Interface.
  Parameter error: nat.
End Interface.

Module Implementation <: Interface.
  Definition t := bool.
  Definition error: t := false.
  Fail End Implementation.
(* A UserError here is expected, not an uncaught Not_found *)

 Reset error.
 Definition error := 0.
End Implementation.


Module Implementation2 <: Interface.
  Definition t := bool.
  Inductive x := X with y := Y.
  Definition error := X.
  Fail End Implementation2.

  Reset error.
  Definition error := Y.
  Fail End Implementation2.

  Reset error.
  Definition error := 0.
End Implementation2.
