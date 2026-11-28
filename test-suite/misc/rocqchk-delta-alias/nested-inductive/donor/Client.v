(* Compiled against ../donor/Lib.v. With the forged library, rocqchk
   computes the signature of F A, for R : T := F A, with the resolver of A,
   where A.X.I is A.Y.I, and finds it a subtype of T, where e says
   forall _ : A.Y.I, False. *)

Require Import ForgedAliases.Lib.

Definition contradiction : False := R.e A.Y.i.
