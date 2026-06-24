(* -*- coq-prog-args: ("-impredicative-set"); -*- *)
Definition impred_def : Set := forall X : Set, X -> X.
Inductive impred_ind : Set := mk_impred : (forall X : Set, X) -> impred_ind.
Inductive normal_ind : Set := mk_normal : True -> normal_ind.
