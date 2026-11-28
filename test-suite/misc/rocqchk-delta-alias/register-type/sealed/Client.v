(* The forged copy gives z the body Int 0, of type M.int once M.int is
   registered as the int63 type, and records the forged Lib.vo as its
   dependency. Then boom is a closed proof of False. z is in a client,
   which rocqchk checks with all of Lib's registrations in force, even a
   rocqchk that drops M's registration at the end of M within Lib. *)

Require Import RegisterType.Lib.

Axiom z : M.int.

Definition boom : False := M.int_empty z.
