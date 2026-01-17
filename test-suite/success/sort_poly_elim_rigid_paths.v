Sort s s' s''.

Constraint s -> s'.
Constraint s' -> s''.

Polymorphic Axiom ad@{s;u} : forall A : Univ@{s;u}, A.
Polymorphic Definition t@{s s';u v|s -> s'} (A : Univ@{s;u}) (B : Univ@{s';v}) : A := ad A.

(* This should succeed even though [s -> s''] is not declared *)
Check t@{s s'';Set Set}.

(* This should fail though as we don't have [s'' -> s'] or [s'' -> s] declared. *)
Fail Check t@{s'' s';Set Set}.
Fail Check t@{s'' s;Set Set}.

(* But if we do this, both should work. *)
Constraint s'' -> s.
Check t@{s'' s';Set Set}.
Check t@{s'' s;Set Set}.
