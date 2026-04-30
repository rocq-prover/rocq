Tactic Notation (at level 4) "test" := idtac "A".
Tactic Notation (at level 5) "test" := idtac "B".

Goal True.
Proof.
test.
Abort.
