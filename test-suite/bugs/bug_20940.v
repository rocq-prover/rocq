(* Was an anomaly List.chop in the presence of projections with not enough argument scopes *)
Record R (n:nat) (p: unit) (q : unit) := { field : unit }.
Arguments field n%_nat {p} {q}.
Check fun C => C.(field _).
