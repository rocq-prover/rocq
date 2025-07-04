Set Universe Polymorphism.
Inductive foo@{s;} : Type@{s;0} := XX.

Fail Fixpoint bar@{s;} (f:foo@{s;}) : True := I.
