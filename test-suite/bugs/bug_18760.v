Module Import M.
  #[local] Reserved Notation "!".
  Inductive I := C : I
  where "!" := I.
  #[local] Reserved Notation "!!".
  Fixpoint f (n : nat) := n where "!!" := f.
End M.
Print I.
Print f.

Module N.
  #[local] Reserved Notation "&".
  Reserved Notation "&".
  Inductive J := D : J where "&" := J.
End N.
Import N.
Check D.
