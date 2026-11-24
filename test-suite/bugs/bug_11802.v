Inductive A (T : Prop) : Prop := B (_ : T).
Scheme Equality for A.
Check A_eq_dec.

Module M.
Set Keep Proof Equalities.
Inductive A (T : Prop) : Prop := B (_ : T).
Scheme Equality for A.
Check A_eq_dec.
End M.
