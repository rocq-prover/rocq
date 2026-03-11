Definition b := 0.
Search _ in TestSearchOpenMod.
Module A.
Definition a := 42.
Search _ in A. (* a: nat *)
Search _ in TestSearchOpenMod.A. (* a: nat *)
Definition improbable_name12345 := 41.
Search "improbable_name12345" inside A.
Search "improbable_name12345" in TestSearchOpenMod.A.
Search "improbable_name12345" outside A.
Search "improbable_name12345" outside TestSearchOpenMod.
End A.
Search _ in TestSearchOpenMod.
Search "improbable_name12345" outside TestSearchOpenMod.
