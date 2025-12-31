Set Universe Polymorphism.
Inductive foo@{s;} : Univ@{s;Set} := XX.

Fail Fixpoint bar@{s;} (f:foo@{s;}) : True := I.
