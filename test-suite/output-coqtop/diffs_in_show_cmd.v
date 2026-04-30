(* -*- coq-prog-args: ("-color" "on"); -*- *)
Goal forall n m:nat, n = m.
Proof.
refine ?[foo].
intros.

Set Diffs "on".
(* diffs should appear identically on each of these in coqtop: *)
Show.
Show 1.
Show Diffs foo.

Abort.
