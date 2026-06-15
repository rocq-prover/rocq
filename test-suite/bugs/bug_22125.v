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
