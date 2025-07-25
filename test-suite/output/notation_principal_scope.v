Arguments conj {_ _} _ _%_function.

Set Warnings "+inconsistent-scopes".
Fail Abbreviation pp X := (conj X X).

Fail Abbreviation pp := 1 (only printing).

Fail Abbreviation pp X := nonexisting.

Fail Abbreviation pp X := (conj X X) (X, X in scope nat_scope).

Abbreviation pp X := (conj X X) (X in scope nat_scope).

Notation "$" := I (only parsing) : nat_scope.
Notation "$" := (I I) (only parsing) : bool_scope.

Open Scope bool_scope.
Check pp $.
Fail Check pp (id $).

Abbreviation pp1 X := (X%nat) (X in scope bool_scope).
Abbreviation pp2 X := ((X + X)%type) (X in scope bool_scope).
Abbreviation pp3 X := (((X, X)%type, X)%nat) (X in scope bool_scope).
