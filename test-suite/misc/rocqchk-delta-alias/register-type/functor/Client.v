(* The forged copy gives z the body Int 0, of type R.M.int once R.M.int is
   registered as the int63 type, and records the forged Lib.vo as its
   dependency. Then boom is a closed proof of False: R.M.int_empty is N's.
   z is in a client so that rocqchk checks all of Lib, with its
   registration, before it types Int 0. *)

Require Import RegisterType.Lib.

Axiom z : R.M.int.

Definition boom : False := R.M.int_empty z.
