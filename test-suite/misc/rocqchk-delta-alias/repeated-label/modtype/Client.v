(* The forged copy records the forged Lib.vo as its dependency. *)

Require Import RepeatedLabel.Lib.

Module M : T.
  Definition t := unit.
End M.
