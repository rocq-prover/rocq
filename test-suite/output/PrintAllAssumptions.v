(** Test for Set Printing All Assumptions *)
Require Import TestSuite.impred_set_prereq.

(** Without the flag, impredicative_set is not in the current env,
    so Print Assumptions hides the theory dependency *)
Print Assumptions impred_def.

(** With the flag, per-definition theory info is shown *)
Set Printing All Assumptions.
Print Assumptions impred_def.

(** Inductive that uses impredicative Set should show it *)
Print Assumptions impred_ind.

(** Inductive that does not use impredicative Set should not show ImpredicativeSet axiom *)
Print Assumptions normal_ind.
