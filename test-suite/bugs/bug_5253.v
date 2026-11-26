Require Import Corelib.Classes.Morphisms.

Fail Global Instance:Proper iff True | 2 Proof.
Fail Instance bar : Reflexive (@eq nat) | 2 nonexistent := _.
Fail Declare Instance baz : Reflexive (@eq nat) | 2 nonexistent.
Fail #[program] Instance qux : Reflexive (@eq nat) | 2 nonexistent := _.

Instance foo {A} : Reflexive (@eq A) | 2 (Reflexive ?a).
Proof. intros ?; reflexivity. Defined.
