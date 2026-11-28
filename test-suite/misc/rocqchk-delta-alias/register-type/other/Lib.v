(* The forged copy registers Base.int, a constant of the earlier library
   Base, as the int63 type. *)

Require Import RegisterType.Base.

(* A declaration that names Base.int, for forge.ml. *)
Definition uses : Set := int.
