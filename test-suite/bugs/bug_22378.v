Inductive sUnit : SProp := stt.

Inductive pair_with_lets : Type :=
| pack (x y : bool)
    (ghost1 : sUnit := stt) (ghost2 : sUnit := stt).

Definition left (p : pair_with_lets) : bool :=
  match p with pack x y ghost1 ghost2 => x end.

Definition right (p : pair_with_lets) : bool :=
  match p with pack x y ghost1 ghost2 => y end.

Fail
Definition collision (p : pair_with_lets) :
  left p = right p := eq_refl.

(*
Theorem contradiction : False.
Proof.
  pose proof (collision (pack true false)) as h.
  cbn in h.
  discriminate h.
Qed.

Print Assumptions contradiction.
*)
