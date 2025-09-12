Inductive loop := L { deloop : loop }.

Module M1.
  (* succeeds producing fix f := f0 _ with f0 := f0 _ for f *)
  Definition f := fix f (t : loop) : False := f (deloop t) with f (t : loop) := f (deloop t) for f.
End M1.
Module M2.
  (* Warning: Not a fully mutually defined fixpoint (f and f are not mutually dependent).
     then fails with "f already exists" (because we try to add 2 constants named f) *)
  Fail Fixpoint f (t : unit) := 0 with f (t : unit) := 1.
End M2.

Module M3.
  (* stack overflow *)
  Fail Fixpoint f _ := _ with f _ := _.
End M3.
Module M4.
  (* stack overflow *)
  Fail Fixpoint f (t : loop) := f (deloop t) with f (t : loop) := f (deloop t).
End M4.
