Class Need := B {  }.

Hint Extern 0 Need => abstract constructor : typeclass_instances.

Definition satisfy (H : Need) : unit := let 'B := H in tt.
Definition wrap {A} (H : Need) (x : A) : A := let 'B := H in x.

Fixpoint fixdef (n : nat) : unit := match n with
| 0 => tt
| S n => fixdef (wrap _ n)
end.

Axiom axmdef : satisfy _ = tt.
