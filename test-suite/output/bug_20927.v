Inductive vec : nat -> Type := vnil : vec 0 | vcons n : nat -> vec n -> vec (S n).
Fail Program Definition f n (v : vec n) : nat := match v with vnil => 0 | vcons _ x _ => x end.
