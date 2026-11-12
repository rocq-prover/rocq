Set Printing Width 400.
Notation "b1 && b2" := (if b1 then b2 else false).
Locate "&&".

Module M.

Notation "'U' t" := (S t) (at level 2).
Notation "'_' t" := (S t) (at level 2).
Locate "U". (* was wrongly returning also "'_' t" *)
Locate "_".

End M.

Module N.

(* Was not working at some time *)
Locate "( t , u , .. , v )".

(* Was working though *)
Locate "( _ , _ , .. , _ )".

(* We also support this *)
Locate "( t , u )".
Locate "( t , u , v )".

End N.

Module O.

(* A notation parsed as a number has no grammar rule: was an anomaly *)
Declare Scope foo_scope.
Notation "1" := true : foo_scope.
Locate "1".

End O.
