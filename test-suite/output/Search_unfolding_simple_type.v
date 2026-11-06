Module M.
Definition T := nat.
Definition one : T := 1.

Search nat in M.
Set Search Mod Unfolding.
Search nat in M. (* New: one *)
End M.
