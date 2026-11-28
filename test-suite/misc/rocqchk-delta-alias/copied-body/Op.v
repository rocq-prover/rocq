(* Two opaque proofs of one type, copied by an Include. coqc makes H.o1 a
   definition of F.o1 and H.o2 one of F.o2, each copy an alias of its
   proof. *)

Module F.
  Lemma o1 : unit. Proof. exact tt. Qed.
  Lemma o2 : unit. Proof. exact tt. Qed.
End F.

Module H.
  Include F.
End H.
