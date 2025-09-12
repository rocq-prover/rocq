Module Import A.
  Module B.
    Abbreviation x := tt.
  End B.
End A.
Check B.x. (* should say tt *)

Module A'.
  Module B'.
    #[global] Abbreviation x := tt.
  End B'.
End A'.
Check tt. (* should say A'.B'.x *)

Import B.
Check tt. (* should say x *)

Import A'.B'.
Check tt.
(* should say B.x (qualified because "x" is short name for B'.x, but
   B'.x not used for printing because the printing rule didn't get
   replayed by Import so is still shadowed by B.x) *)

Disable Notation B.x.

Check tt.
(* should say x *)
