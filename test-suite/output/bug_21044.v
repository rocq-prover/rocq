Class A (P Q : Prop) := {}.
Instance a {P Q} : A P Q := {}.
Hint Mode A - - : typeclass_instances.

Class B (P Q : Prop) := {}.
Hint Mode B - ! : typeclass_instances.

Axiom foo : forall {P Q},
  A P Q ->
  B P Q -> True.

Set Typeclasses Debug Verbosity 1.
Check foo _ _ _ _ _ _ _ _ _ _ _.
