Primitive Blocked@{s;u} : Type@{s;u} -> Type@{s;u} := #blocked_type.

Primitive block@{s;u} : forall (T : Type@{s;u}), T -> Blocked@{s;u} T := #block.
#[global] Arguments block {_} _.

Primitive unblock@{s;u} : forall (T : Type@{s;u}), Blocked@{s;u} T -> T := #unblock.
#[global] Arguments unblock {_} _.

Primitive run@{s sk;u uk | s -> sk} : forall (T : Type@{s;u}) (K : Type@{sk;uk}), Blocked@{s;u} T -> (T -> K) -> K := #run.
#[global] Arguments run {_ _} _ _.

Primitive Blocked_ind@{s sp;u up | s -> sp} :
  forall
    (T : Type@{s;u})
    (P : Blocked@{s;u} T -> Type@{sp;up})
    (IH : forall t:T, P (block@{s;u} t)),
    forall b, P b := #blocked_ind.
#[global] Arguments Blocked_ind {_ _} _ _.
