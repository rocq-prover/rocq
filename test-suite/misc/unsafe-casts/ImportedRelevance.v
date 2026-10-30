From UnsafeCasts Require Import Relevance.

(* Repeat the metadata and helper checks against serialized declarations. *)
Check (0 <:["test.relevance-metadata"] nat).
Definition imported_irrelevant := let p := relevance_indirect in p.
Definition imported_relevant := let p := relevance_relevant in p.
Definition imported_function := let p := relevance_fun_indirect in p.
