(* Compiled against ../donor/Lib.v. In the forged library, M2.f says
   M2.c = false, and M2.c's canonical name is M1.c. *)

Require Import ForgedAliases.Lib.

Definition boom : eq bool true false :=
  match M2.f in eq _ _ y return eq bool true y with
  | eq_refl _ _ => M1.e
  end.

Definition contradiction : False :=
  match boom in eq _ _ y return discr y with
  | eq_refl _ _ => I
  end.
