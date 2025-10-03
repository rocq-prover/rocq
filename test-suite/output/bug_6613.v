Ltac foo n := idtac.

Ltac bar := foo constr:(5).

Print Ltac bar.
