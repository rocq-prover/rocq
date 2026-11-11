Unset Strict Universe Declaration.

Module SideEffects.

Inductive nat := O | S (n : nat).

Record prod (A B : Type) := { fst : A; snd : B }.

Lemma prod_rect (A:nat -> Type@{i}) (B:nat->Type@{j} )
      (ab0 : prod (A O) (B O))
      (sab : forall n, prod (A n) (B n) -> prod (A (S n)) (B (S n)))
  : forall n, prod (A n) (B n).
Proof.
  induction n.
  - abstract exact ab0.
  - apply sab;exact IHn.
Qed.

Lemma foo : Type.
Proof.
abstract exact Set.
Defined.

Lemma foo' : Type.
Proof.
abstract exact Set.
Qed.

End SideEffects.

Module Modules.

Module Type Typ.
  Parameter  t : Type.
End Typ.

Module Type HasEq (Import T:Typ).
  Parameter  eq : t -> t -> Prop.
End HasEq.

Module Type Eq := Typ <+ HasEq.

Module Type ES.
Parameter A : Type.
Parameter eq : A -> A -> Type.
End ES.

Module Make
  (AX : Typ)
  (X : ES with Definition A := AX.t with Definition eq := @eq AX.t).
End Make.

End Modules.

Module Mutual.

Fixpoint F (n : nat) (A : Type) {struct n} : nat
with G (n : nat) (A : Type) {struct n} : nat.
Proof.
- destruct n; [exact 0|exact (G n A)].
- destruct n; [exact 0|exact (F n A)].
Defined.

Inductive even : nat -> Type :=
| evenO : even 0
| evenS : forall n, odd n -> even (S n)
with odd : nat -> Type :=
| oddS : forall n, even n -> odd (S n).

Scheme even_ind_type := Induction for even Sort Type
with odd_ind_type := Induction for odd Sort Type.

End Mutual.
