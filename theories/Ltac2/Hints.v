Require Import Ltac2.Init.
From Ltac2 Require Import Message.
From Ltac2 Require Import Printf.

(* Abstract type for hint *)
Ltac2 Type hint.

Ltac2 @ external get_hints: string -> (hint list) option := "rocq-runtime.plugins.ltac2" "get_hints".

Ltac2 @ external run_hint: hint -> unit := "rocq-runtime.plugins.ltac2" "run_hint".

(*
Ltac2 @ external foo : unit -> list hint :=
  "rocq-runtime.plugins.ltac2" "get_hints".
  *)
