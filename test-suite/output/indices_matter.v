(* -*- coq-prog-args: ("-indices-matter"); -*- *)
Require Import TestSuite.indices_matter_prereq.

Print Assumptions M.X.

(* Test Set Indices Matter *)
Module SetIndicesMatter.
  Set Indices Matter.
  Print Assumptions M.X.
  Unset Indices Matter.
  Print Assumptions M.X.
End SetIndicesMatter.
