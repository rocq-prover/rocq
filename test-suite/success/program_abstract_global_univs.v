Unset Universe Polymorphism.
Universes a b.
Definition Ta := Type@{a}.
Definition Tb := Type@{b}.

(* The constraint a <= b found by the abstracted proof must be declared with the obligation,
   in which the side effect is inlined *)
Program Definition foo : Ta -> Tb := _.
Next Obligation.
  abstract (exact (fun x => x)).
Defined.
Fail Constraint b < a.
