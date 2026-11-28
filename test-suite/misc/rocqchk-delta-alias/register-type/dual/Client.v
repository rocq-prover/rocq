(* The forged copy gives z the body Int 0 and records the forged Lib.vo as
   its dependency. With N.int as the canonical name of the registered int,
   Int 0 has a type that converts with N.int, and boom is a closed proof of
   False. z is in a client because rocqchk puts the registration in force
   under that canonical name only after Lib. *)

Require Import RegisterType.Lib.

Axiom z : N.int.

Definition boom : False := match z return False with end.
