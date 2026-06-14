(* Test that fixpoints whose structural argument type involves
   a section Let-bound variable pass rocqchk *)
Section S.
Let T := list nat.
Fixpoint my_length (l : T) : nat :=
  match l with
  | nil => O
  | cons _ l' => S (my_length l')
  end.
End S.
