(* Test that fixpoints whose structural argument type involves
   a let-bound variable are accepted by the guard checker *)
Section S.
Let T := list nat.
Fixpoint my_length_sec (l : T) : nat :=
  match l with
  | nil => O
  | cons _ l' => S (my_length_sec l')
  end.
End S.

Definition my_length (T:=list nat) := fix my_length (l : T) : nat :=
  match l with
  | nil => O
  | cons _ l' => S (my_length l')
  end.


(* Proof of False because of the original misalignment *)

Inductive T : Prop := C (f : forall A : Prop, A -> A) | D (x : T).
Inductive Loop : Prop := loop (deloop : Loop) | loop2 (deloop : Loop).

Fail
Definition rec (T2 := T) (T1 := Loop) := fix rec (x : T2) : False :=
  match x with C f => rec (f _ x) | D x => rec x end.

(* Definition false : False := rec (C idProp). *)
