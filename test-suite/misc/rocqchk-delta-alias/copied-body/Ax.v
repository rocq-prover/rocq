(* Two axioms of one type, copied by an Include. coqc makes H.a1 a
   definition of F.a1 and H.a2 one of F.a2, each copy an alias of its
   axiom. *)

Inductive unit : Set := tt.

Module F.
  Axiom a1 : unit.
  Axiom a2 : unit.
End F.

Module H.
  Include F.
End H.
