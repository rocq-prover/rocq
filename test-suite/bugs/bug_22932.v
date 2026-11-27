(* -*- coq-prog-args: ("-impredicative-set"); -*- *)

Set Universe Polymorphism.

Inductive BigBox@{s; u|} (A : Univ@{s; u}) : Set :=
| bigbox (_ : A).

Check BigBox_rec.
Fail Check BigBox_rect.

(* Eliminating into Set is still allowed (SquashToSet). *)
Definition bigbox_to_set@{s; u|} (A : Univ@{s; u}) (P : Set) (f : A -> P)
  (x : BigBox@{s; u} A) : P :=
  match x with bigbox _ a => f a end.

(* Eliminating into Type@{>Set} (e.g. Set : Type) must be rejected. *)
Fail Definition up@{u | Set < u} (x : BigBox@{Type; u} Set) : Set :=
  match x with bigbox _ A => A end.

(* Small sort-polymorphic arguments in Set remain unsquashed. *)
Inductive SmallBox@{s; |} (A : Univ@{s; Set}) : Set :=
| smallbox (_ : A).

Check SmallBox_rect.

Definition unsmall@{s; |} (A : Univ@{s; Set}) (x : SmallBox@{s;} A) : A :=
  match x with smallbox _ a => a end.
