Require Import Ltac2.Ltac2.

Goal True /\ False.
  (* conversion works *)
  if Unification.conv_full '4 '(2 + 2)
  then ()
  else Control.throw (Tactic_failure None).
  (* conversion fails *)
  if Unification.conv_full '4 '3
  then Control.throw (Tactic_failure None)
  else ().
  (* must be focussed *)
  split. Fail all: Unification.conv_full '4 '(2 + 2).
Abort.
