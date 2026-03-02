Sort s.

Inductive Ind1 : Type@{s; _} := C.
(* Universe inconsistency. Cannot enforce Prop <= Type@{s | Set}. *)

Fail #[universes(template)] Inductive ofTy A : Type@{s; _} := OfTy (_:A).
(* not yet implemented *)

Inductive ofTy A : Type@{s;_} := OfTy (_:A).

(* parameter A was inferred to be in sort s *)
Check ofTy Ind1.
