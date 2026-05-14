Primitive Blocked@{s;u} : Type@{s;u} -> Type@{s;u} := #blocked_type.

Primitive Blocked_ind@{s sp;u up | s -> sp} :
  forall
    (T : Type@{s;u})
    (P : Blocked@{s;u} T -> Type@{sp;up})
    (IH : forall t:T, P (__block@{s;u} T t)),
    forall b, P b := #blocked_ind.
#[global] Arguments Blocked_ind {_ _} _ _.
