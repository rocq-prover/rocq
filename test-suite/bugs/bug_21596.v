Axiom coe : nat -> bool.
Coercion coe : nat >-> bool.

Abbreviation foo := (fun x => true = x /\ x = 0 :> nat).

Check @foo : nat -> Prop.
