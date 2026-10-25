(* The literal's type is available only through the registered primitive type.
   The report must include that type as well as the rewrite-rule symbol. *)

From Corelib Require Import PrimInt63.

Symbol T : Set.
Rewrite Rule T_int := T => int.
Definition i : T := 0%uint63.
