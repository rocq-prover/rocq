Declare ML Module "unsafe_cast.plugin".

Inductive strict : SProp := strict_proof.

(* Proposed policy: arbitrary type comparisons may be trusted, but a cast
   must preserve relevance. Same-relevance casts remain supported. *)
Definition accepted_relevant : False := 0 <:["test.accept"] False.
Definition accepted_irrelevant : strict := strict_proof <:["test.accept"] strict.
Definition let_relevant := let p := (0 <:["test.accept"] False) in p.
Definition let_irrelevant :=
  let p := (strict_proof <:["test.accept"] strict) in p.

(* This test-only handler independently probes the kernel in both directions.
   It must not be enough to reject these casts only during elaboration. *)
Check (0 <:["test.relevance-regression"] nat).

(* Check exercises elaboration without relying on declaration-time checking;
   Definition must also refuse to create inconsistent const_relevance data. *)
Fail Check (0 <:["test.accept"] strict).
Fail Check (strict_proof <:["test.accept"] nat).
Fail Definition relevant_to_strict : strict := 0 <:["test.accept"] strict.
Fail Definition strict_to_relevant : nat := strict_proof <:["test.accept"] nat.
