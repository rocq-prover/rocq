(* A premise p + a of a clause c + k <= max(P) is dropped when p + a <= max(P \ {p}, c + k - 1)
   holds: it is below another premise, or strictly below the conclusion, and the clause is
   equivalent to the one on the remaining premises. *)

(* The dominating clauses come first: u0 <= max(t, d1, d2+1) is u0 <= d1, as t <= d1 and d2 < d1 *)
Universes t d1 d2 u0.
Constraint t <= d1, d2 < d1.
Constraint u0 <= max(t, d1, d2+1).
Print Universes Subgraph (t d1 d2 u0).

(* The dominating clauses come after: the clause is simplified again when they are added *)
Universes t' e1 e2 v0.
Constraint v0 <= max(t', e1, e2+1).
Constraint t' <= e1.
Constraint e2 < e1.
Print Universes Subgraph (t' e1 e2 v0).

(* Transitively: once a <= y, the premise a of b <= max(a, y) is dominated too *)
Universes a b x y.
Constraint a <= max(x, y).
Constraint b <= max(a, y).
Constraint x <= y.
Print Universes Subgraph (a b x y).

(* A premise strictly below the conclusion can never be the maximum: c < max(p, q) and p <= c give
   c < q, as u+1 <= max(u, v) is u+1 <= v *)
Universes c p q.
Constraint c < max(p, q).
Constraint p <= c.
Print Universes Subgraph (c p q).

(* Through a clause with several premises: p' <= max(s, w) with s, w <= q' gives p' <= q', so
   g <= max(p', q') is g <= q' *)
Universes g p' q' s w.
Constraint s <= q', w <= q'.
Constraint p' <= max(s, w).
Constraint g <= max(p', q').
Print Universes Subgraph (g p' q' s w).

(* Below the maximum of two other premises: h <= max(i, j, l) with i <= max(j, l) is h <= max(j, l) *)
Universes h i j l.
Constraint i <= max(j, l).
Constraint h <= max(i, j, l).
Print Universes Subgraph (h i j l).
