(* Unifying two applications of the same primitive projection does not identify the universes of
   the types of the records once these are unified: [mk@{u Set} A] and [mk@{u u} A] are
   convertible, as [mk] does not depend on its second universe, but their types are not. *)
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Primitive Projections.

Record Rig@{c e} := { car : Type@{c}; eqv : car -> car -> Type@{e}; op : car -> car -> car }.
Definition mk@{c e} (A : Type@{c}) : Rig@{c e} :=
  {| car := A; eqv := fun _ _ => unit; op := fun x _ => x |}.
Opaque mk.
Axiom op_resp@{c e} : forall (r : Rig@{c e}) (x : car r), eqv r (op r x x) (op r x x).

Section S.
  Universe u.
  Context (A : Type@{u}) (a : A).
  (* [apply] unifies [?r] with [mk@{u u} A], then [op ?r] with [op (mk@{u Set} A)] *)
  Definition t : eqv (mk@{u u} A) (op (mk@{u Set} A) a a) (op (mk@{u Set} A) a a).
  Proof. apply op_resp. Defined.
End S.

Definition t_above@{v | Set < v} := t@{v}.
