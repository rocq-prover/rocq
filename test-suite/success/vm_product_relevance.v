(* Direct readback of a product with a statically irrelevant binder. *)
Definition product_irrelevant (A : SProp) := Eval vm_compute in (A -> Set).
Check fun A => eq_refl : product_irrelevant A = (A -> Set).

Set Universe Polymorphism.

Definition product@{q;u|} (A : Univ@{q;u}) := A -> A.

(* The same bytecode must produce different binder relevances at different
   quality instances, including when that instance is still abstract. *)
Definition product_type (A : Set) := Eval vm_compute in product@{Type;Set} A.
Definition product_sprop (A : SProp) := Eval vm_compute in product@{SProp;Set} A.
Definition product_poly@{q;u|} (A : Univ@{q;u}) :=
  Eval vm_compute in product@{q;u} A.

Check fun A => eq_refl : product_type A = (A -> A).
Check fun A => eq_refl : product_sprop A = (A -> A).
Check fun A => eq_refl : product_poly A = (A -> A).
