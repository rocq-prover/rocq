Declare ML Module "unsafe_cast.plugin".

Inductive strict : SProp := strict_proof.

(* Arbitrary type comparisons may be trusted, but a cast
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

(* A direct-cast guard is not sufficient. These type-level casts preserve the
   relevance of the type values themselves, but change the sorts of types
   used by later definitions. Cached relevance must follow their checked types. *)
Definition relevance_strict_type : SProp := nat <:["test.accept"] SProp.
Definition relevance_indirect : relevance_strict_type := 0.
Definition relevance_let_indirect := let p := relevance_indirect in p.
Definition relevance_inferred :=
  ((fun _ : nat => 0) : nat -> relevance_strict_type) 0.

Definition relevance_relevant_type : Set := strict <:["test.accept"] Set.
Definition relevance_relevant : relevance_relevant_type := strict_proof.
Definition relevance_let_relevant := let p := relevance_relevant in p.

Definition relevance_type_fun : nat -> SProp :=
  (fun _ : nat => nat) <:["test.accept"] (nat -> SProp).
Definition relevance_fun_indirect : relevance_type_fun 0 := 0.
Definition relevance_fun_let := let p := relevance_fun_indirect in p.

Section LocalDefinition.
  Let p : relevance_strict_type := 0.
  Let inferred_p := ((fun _ : nat => 0) : nat -> relevance_strict_type) 0.
  Definition relevance_local := let q := p in q.
  Check (0 <:["test.relevance-metadata"] nat).
End LocalDefinition.

(* This independently compares stored metadata, kernel typing, and both
   relevance helpers, including casts under binders and application types. *)
Check (0 <:["test.relevance-metadata"] nat).

Module Quality.
  Set Universe Polymorphism.
  Definition same@{q;u} (A B : Univ@{q;u}) (a : A) : B :=
    a <:["test.accept"] B.
  Fail Definition change@{q;u} (A : Univ@{q;u}) (a : A) : nat :=
    a <:["test.accept"] nat.
  Definition known_relevant@{q;u|q -> Prop} (A : Univ@{q;u}) (a : A) : nat :=
    a <:["test.accept"] nat.
  Definition irrelevant_instance : strict := same@{SProp;Set} strict strict strict_proof.
  Definition relevant_instance : nat := same@{Type;Set} nat nat 0.
End Quality.
