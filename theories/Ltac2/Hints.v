Require Import Ltac2.Init.

(* Abstract types for hint and hint_db *)
Ltac2 Type hint_db.
Ltac2 Type hint.

Ltac2 @ external get_hint_db: string -> (hint_db) option :=
    "rocq-runtime.plugins.ltac2" "get_hint_db".

Ltac2 @ external get_applicable_hints: hint_db -> hint list :=
    "rocq-runtime.plugins.ltac2" "get_applicable_hints".


(* TODO: Add different strategies for running hints - auto / eauto / tc_eauto *)
Ltac2 @ external run_hint: hint -> unit := "rocq-runtime.plugins.ltac2" "run_hint".
