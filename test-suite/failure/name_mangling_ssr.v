Set Mangle Names.
Set Mangle Names Light.
Set Mangle Names Prefix "‗".
Set Mangle Names Suffix "‗".


Require Import ssreflect.
Goal forall (H:True), True.
Proof.
  intro.
  Fail exact ‗H‗.
Admitted.
