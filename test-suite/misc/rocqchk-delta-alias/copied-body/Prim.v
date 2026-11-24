(* Two primitive operators of one type, copied by an Include. coqc makes
   H.add a definition of F.add and H.sub one of F.sub, each copy an alias
   of its operator. *)

Primitive int := #int63_type.

Module F.
  Primitive add := #int63_add.
  Primitive sub := #int63_sub.
End F.

Module H.
  Include F.
End H.
