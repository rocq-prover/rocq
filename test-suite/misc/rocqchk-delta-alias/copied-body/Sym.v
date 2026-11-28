(* Two symbols of one type, copied by an Include. coqc makes H.s1 a
   definition of F.s1 and H.s2 one of F.s2, each copy an alias of its
   symbol. *)

Inductive unit : Set := tt.

Module F.
  Symbol s1 : unit.
  Symbol s2 : unit.
End F.

Module H.
  Include F.
End H.
