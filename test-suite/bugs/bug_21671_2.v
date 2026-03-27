
Reserved Notation "T x = A ; b" (at level 200, b at level 200, format "T  x  =  A ; '//' b").

Axiom LetIn : forall {tx:nat} (a b : nat), nat.

Notation "T x = A ; b" := (LetIn (tx:=T) A (fun x => b)).
(* fails to parse *)
