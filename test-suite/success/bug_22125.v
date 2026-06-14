(* Test that fixpoints whose structural argument type involves
   a let-bound variable are accepted by the guard checker *)
Definition my_length (T:=list nat) := fix my_length (l : T) : nat :=
  match l with
  | nil => O
  | cons _ l' => S (my_length l')
  end.
