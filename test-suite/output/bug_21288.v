Ltac foo := (intuition idtac) || fail "boom".
Ltac bar := intuition idtac || fail "baam". (* parsed as [intuition (idtac || fail "baam")] *)

Print Ltac foo.
(* printed without parentheses, ie equivalent to bar *)

Print Ltac bar.

Goal True -> 2 = 3.
Proof.
  (* yet foo is not equivalent to bar ( "||" runs the second tactic if the first doesn't make progress) *)
  Succeed foo.
  Fail bar.
Abort.
