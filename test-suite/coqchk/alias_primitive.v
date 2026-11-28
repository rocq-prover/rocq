(* -*- coq-prog-args: ("-noinit"); -*- *)

(* A module alias and an Include copy a primitive operator. Strengthening
   makes each copy a definition of the operator, under the operator's
   canonical name (Modops.strengthen_const), so rocqchk must accept the
   copies as coqc does. *)

Primitive int := #int63_type.

Module F.
  Primitive add := #int63_add.
End F.

Module G := F.

Module H.
  Include F.
End H.
