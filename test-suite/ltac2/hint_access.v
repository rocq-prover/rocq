From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Hints.
From Ltac2 Require Import List.
From Ltac2 Require Import Option.

(* This is printing the number of hints in the core database *)
Ltac2 Eval (List.length (Option.get (Hints.get_hints "core"))).

Parameter P : Prop.
Parameter p  : P.

Create HintDb custom.
Hint Resolve p : custom.

Goal P. Proof.
    Hints.run_hint (List.hd (Option.get (Hints.get_hints "custom"))).
Qed.
