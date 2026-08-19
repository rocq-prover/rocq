Require (safe) CMorphisms. (* depends on CRelationClasses *)

(* no implicit arguments, but can be used *)
Type CRelationClasses.flip.
About CRelationClasses.flip.
Print CRelationClasses.flip.

(* could do a full require of safe-required deps instead but needs more work *)
Fail Require SetoidTactics.
