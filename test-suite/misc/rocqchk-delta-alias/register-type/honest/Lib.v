(* Each primitive type is registered as coqc registers it, by Primitive: int
   in the sealed module MI, the others at the top. lit, after MI, is an
   int63 literal, whose type is the int that MI registered. The forged copy
   (case twice) registers MI.int a second time. *)

Module Type IT.
  Parameter int : Set.
End IT.

Module MI : IT.
  Primitive int := #int63_type.
End MI.

Primitive float := #float64_type.
Primitive string := #string_type.
Primitive array := #array_type.

Primitive max_length := #array_max_length.

Definition lit := Eval compute in max_length.
