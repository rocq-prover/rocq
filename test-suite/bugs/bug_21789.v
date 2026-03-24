Inductive sTrue : SProp := stt.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.
Record foo := { bar : sTrue }.
(* Error:
In environment
P : foo -> Type
Build_foo : forall bar : sTrue, P (Build_foo bar)
f : foo
The term "let f0 : foo := f in let bar := test.bar f0 in Build_foo bar"
has type "P (test.Build_foo (test.bar f))" while it is expected to have type
 "P f".*)
