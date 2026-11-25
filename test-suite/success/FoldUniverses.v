(* [fold] identifies subterms that differ by the instances of flexible
   universes, as cumulativity introduces copies of them. *)

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Record box@{u} := Box { unbox : Type@{u} }.

Definition idb@{u} (b : box@{u}) : box@{u} := b.

Lemma fold_copy@{u} (b : box@{u}) : idb@{u} b = idb@{u} b.
Proof.
  (* The body of [c] is [idb@{v} b], with a fresh [v] such that [u <= v] *)
  pose (c := idb b).
  fold c.
  match goal with |- c = c => reflexivity end.
Qed.
