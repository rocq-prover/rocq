Set Universe Polymorphism.

Axiom A@{s;} : Type@{s;Set}.

Definition prod@{s;} := A@{s;} -> Prop.

Definition foo@{s s';} := Eval lazy head in prod@{s';}.
(*  Binder (_ : "A") has relevance mark set to a variable β0 but was expected to be a variable β1 *)
