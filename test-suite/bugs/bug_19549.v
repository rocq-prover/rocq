Notation "'lam' a := b" := (fun 'a => b) (a pattern, at level 10, only parsing).

Ltac foo := let c := open_constr:(lam sum := sum) in c.
Print foo.

Ltac baz := let c := open_constr:(fun '(S _ as k) => k) in c.
Print baz.
