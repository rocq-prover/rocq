Inductive A (X : Type) : Type := a : X -> A X | a' : B X -> A X with B (X : Type) : Type := b : A X -> B X.
Fail Inductive T (P : Type) : Type := C : nat -> A (T P) -> T P.
