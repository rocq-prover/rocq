Set Universe Polymorphism.
Inductive foo@{s;} : Type@{s;Set} := XX.

Fail Fixpoint bar@{s;|} (f:foo@{s;}) : True := I.
