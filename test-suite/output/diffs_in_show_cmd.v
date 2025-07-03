Set Diffs "on".
Goal forall n m:nat, n = m.
refine ?[foo].
intros.

(* diffs should appear identically on each of these: *)
Show.
Show 1.
Show foo.
