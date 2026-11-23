(* The unification of [auto] and [eauto] does not reduce strict subterms,
   but it does expand their keys: a primitive projection of a record that
   has to be unfolded is still reduced there. *)
Set Primitive Projections.
Record chain (A : Type) := { chain_car :> nat -> A }.
Definition chain_map {A B} (g : A -> B) (c : chain A) : chain B :=
  {| chain_car n := g (c n) |}.

Goal forall (A B : Type) (P : A -> Prop) (g : B -> A) (c : chain B) (n : nat),
  (forall y, P (g y)) -> P (chain_map g c n).
Proof.
  intros A B P g c n Pg.
  eauto.
Qed.
