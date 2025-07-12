
Abbreviation foo := ltac:(exact 1).

Abbreviation bar := (2 :> nat).

Abbreviation baz := (3 <: nat).

Check foo.
Check bar.
Check baz.
