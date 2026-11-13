(* The constraints between the kept universes are derived through the universes they bound, even
   when none of their clauses has all its premises bounded: x + 2 <= max(b + 1, b0), hence
   a + 2 <= max(b + 1, b0). *)
Universes a b b0 x p.
Constraint a <= x.
Constraint x < max(p, b).
Constraint p < max(x, b0).
Print Universes Subgraph (a b b0).
