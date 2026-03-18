(* -*- coq-prog-args: ("-impredicative-set"); -*- *)

Definition foo : Set := forall A : Set, A -> A.

Inductive bar : Set := Bar (_:Type).

Check bar_rec.
Fail Check bar_rect.
