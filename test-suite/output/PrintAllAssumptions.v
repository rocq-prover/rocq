(** Test for Set Printing All Assumptions *)
Require Import TestSuite.impred_set_prereq.

(** Without the flag, impredicative_set is not in the current env,
    so Print Assumptions hides the theory dependency *)
Print Assumptions impred_def.

(** Equal displayed output must not hide different theory assumptions. *)
Definition pred_def := 0.
Print Assumptions impred_def pred_def.

(** With the flag, per-definition theory info is shown *)
Set Printing All Assumptions.
Print Assumptions impred_def.
Print Assumptions impred_def impred_def pred_def.
