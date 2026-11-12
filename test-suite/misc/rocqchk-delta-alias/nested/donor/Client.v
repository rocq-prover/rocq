(* Compiled against ../donor/Lib.v. With the forged library, rocqchk
   computes the signature of F A, for R : T := F A, with the resolver of A,
   where A.X.d is A.Y.d, and finds it a subtype of T, where e says
   A.Y.d = false. *)

Require Import ForgedAliases.Lib.

Definition boom : eq bool true false := R.e.

Definition contradiction : False :=
  match boom in eq _ _ y return discr y with
  | eq_refl _ _ => I
  end.
