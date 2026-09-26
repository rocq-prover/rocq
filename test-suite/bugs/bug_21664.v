Sort s.

Inductive Ind1 : Univ@{s; _} := C.
(* Universe inconsistency. Cannot enforce Prop <= Type@{s | Set}. *)

Fail #[universes(template)] Inductive ofTy A : Univ@{s; _} := OfTy (_:A).
(* not yet implemented *)

Inductive ofTy A : Univ@{s;_} := OfTy (_:A).

(* parameter A was inferred to be in sort s *)
Check ofTy Ind1.
