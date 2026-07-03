Set Definitional UIP.

Inductive test : let x := nat in x -> SProp := T : test 0.

Fail Definition bla (e : test 1) := match e in test x1 x2 return x1 with T => 0 end.

Inductive test' : nat -> SProp := T' : test' 0.

Definition bla (e : test' 1) := match e in test' x1 return nat with T' => 0 end.
