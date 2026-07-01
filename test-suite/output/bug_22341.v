Require Extraction.

Polymorphic Definition idp@{s;u} (A : Univ@{s;u}) (a : A) : A := a.

Polymorphic Inductive bli@{s;u} (A:Univ@{s;u}) : Type := { x : A }.

Extraction idp.

Extraction bli.
