Inductive SFalse : SProp := .

Unset Universe Checking.

Definition f g := (g tt : SFalse).
