Inductive T := A | P (a b : T).
Inductive E : T -> Type := L : forall tx, E tx -> E tx.

Definition f {t} (e : E t) : e = e :=
  match e return e = e with
  | L (P _ _) _ => eq_refl
  | L A _ => eq_refl
  end.
