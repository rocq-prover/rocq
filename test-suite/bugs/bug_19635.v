Require Extraction.

Fixpoint f (n:nat) : nat :=
  match n with 0 => 0 | S m => g m end
with g (n:nat) : nat :=
  match n with 0 => 0 | S m => f m end.

Extraction f.
Extraction g.

Module M.
Fixpoint f' (n:nat) : nat :=
  match n with 0 => 0 | S m => g' m end
with g' (n:nat) : nat :=
  match n with 0 => 0 | S m => f' m end.
End M.

Extraction M.g'.
