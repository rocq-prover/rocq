(* The sort can be declared before the squashed inductive *)
Module TestBefore.
  #[universes(polymorphic=no), uip] Sort foo.

  Inductive seq {A : Type} (x : A) : A -> SProp := srefl : seq x x.

  Definition transport {A : Type} {x y : A} {P : A -> Univ@{foo;_}} (e : seq x y) (u : P x) : P y :=
    match e with srefl _ => u end.

  Fail Definition transport_type {A : Type} {x y : A} {P : A -> Type} (e : seq x y) (u : P x) : P y :=
    match e with srefl _ => u end.

  Fail Definition transport_prop {A : Type} {x y : A} {P : A -> Prop} (e : seq x y) (u : P x) : P y :=
    match e with srefl _ => u end.
End TestBefore.

(* Or it can be declared after the squashed inductive *)
Module TestAfter.
  Inductive seq {A : Type} (x : A) : A -> SProp := srefl : seq x x.

  #[universes(polymorphic=no), uip] Sort foo.

  Definition transport {A : Type} {x y : A} {P : A -> Univ@{foo;_}} (e : seq x y) (u : P x) : P y :=
    match e with srefl _ => u end.

  Fail Definition transport_type {A : Type} {x y : A} {P : A -> Type} (e : seq x y) (u : P x) : P y :=
    match e with srefl _ => u end.

  Fail Definition transport_prop {A : Type} {x y : A} {P : A -> Prop} (e : seq x y) (u : P x) : P y :=
    match e with srefl _ => u end.
End TestAfter.

Module ShouldBeUpwardsClosed.
  #[universes(polymorphic=no), uip] Sort foo.
  Monomorphic Constraint foo -> Prop.

  Inductive seq {A : Type} (x : A) : A -> SProp := srefl : seq x x.
  Inductive feq {A : Type} (x : A) : A -> Univ@{foo;_} := frefl : feq x x.

  (* Can always do the transitive encoding. *)
  Lemma seq_to_eq A (x y : A) (e : seq x y) : x = y.
  Proof.
    assert (e' : feq x y).
    - now destruct e.
    - now destruct e'.
  Qed.

  (* Hence, we allow the following: *)
  Lemma seq_to_eq'  A (x y : A) (e : seq x y) : x = y.
  Proof. now destruct e. Qed.
End ShouldBeUpwardsClosed.
