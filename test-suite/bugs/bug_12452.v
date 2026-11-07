Inductive ty : Set := Nat : ty.

Parameter f : ty -> (nat -> nat) -> nat.
Parameter g : ty -> (nat -> bool) -> bool.

Section S.

Variable P1 : ty -> (nat -> nat) -> nat -> Prop.
Variable P2 : ty -> (nat -> bool) -> bool -> Prop.

Variable H1 : forall t h, P1 t h (f t h).
Variable H2 : forall t h, P2 t h (g t h).

Lemma f_ind (t : ty) (h : nat -> nat) : P1 t h (f t h)
with g_ind (t : ty) (h : nat -> bool) : P2 t h (g t h).
Proof.
  - apply H1.
  - apply H2.
Qed.

End S.

Fail Combined Scheme fg_ind from f_ind, g_ind.
