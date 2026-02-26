Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 10, x binder, y binder, P at level 200,
  format "'[  ' '[  ' ∀  x  ..  y ']' ,  '/' P ']'") : type_scope.
(* from Utf8_core.v *)

Definition id {A} (a:A) := a.
About id.
