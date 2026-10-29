Inductive I := S : I -> I.

Axiom V : Set -> Set.

Definition W : I -> Type := fix W (n:I) : Set := match n with S n => V (W n) end.

Axiom n : I.
Definition test := Eval lazy head in W (S n).
(*
Illegal application:
The term "V" of type "Set -> Set" cannot be applied to the term
 "W n" : "Type"
This term has type "Type" which should be a subtype of "Set".
*)
