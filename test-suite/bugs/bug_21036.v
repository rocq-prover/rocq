Definition  OK (b : bool) := if b then True else False.

Inductive Foo (x y:bool) : Prop :=
| is_Foo : let unused := True in OK x -> Foo x y.

Lemma bug (h : OK true) : True.
Proof.
  apply is_Foo in h. (* would generate unbound rel *)
  Validate Proof.
  all:constructor.
Qed.
