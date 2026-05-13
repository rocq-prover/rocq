Primitive Blocked@{s;u} : Type@{s;u} -> Type@{s;u} := #blocked_type.

Primitive block@{s;u} : forall (T : Type@{s;u}), T -> Blocked@{s;u} T := #block.
Primitive unblock@{s;u} : forall (T : Type@{s;u}), Blocked@{s;u} T -> T := #unblock.

Primitive run@{s sk;u uk} : forall (T : Type@{s;u}) (K : Type@{sk;uk}), Blocked@{s;u} T -> (T -> K) -> K := #run.

Arguments block {_} _.
Arguments unblock {_} _.
Arguments run {_ _} _ _.
