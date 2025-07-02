Inductive Foo := foo.
Declare Scope foo_scope.
Delimit Scope foo_scope with foo.
Bind Scope foo_scope with Foo.
Notation "'!'" := foo : foo_scope.
Definition of_foo {x : nat} {y : nat} (f : Foo) := f.
Abbreviation a := (@of_foo O).
Abbreviation b := (@a).
Check a !.
Check @a O !.
Check @b O.
Check @b O !. (* was failing *)
(* All are printed "a !", without making explicit the "0", which is
   incidentally disputable *)
