Module M.
Definition T1 := nat.
Definition T2 := nat.
Definition one : T1 := 1.

Search head:T2 in M.
Set Search Mod Unfolding.
Search head:T2 in M. (* New: one *)
End M.
