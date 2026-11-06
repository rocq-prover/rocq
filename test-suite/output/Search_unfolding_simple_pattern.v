Module M.
Definition one : nat := 1.
Definition T := nat.

Search T in M.
Set Search Mod Unfolding.
Search T in M. (* New: one *)
End M.
