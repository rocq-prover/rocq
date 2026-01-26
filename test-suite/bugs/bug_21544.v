Set Primitive Projections.
Record prod A B := pair { pr1: A; pr2: B }.

Definition f {A B} (p : prod A B) : nat := let '(pair _ _ a b) := p in 0.
Definition g {A B} '(pair _ _ a b : prod A B) : nat := 0.
