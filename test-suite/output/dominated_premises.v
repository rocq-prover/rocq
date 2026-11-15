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

(* The simplified clause is removed when the other ones entail it: k0 <= max(m0, n0) is k0 <= n0 once
   m0 <= n0, which k0 <= m0 entails *)
Universes k0 m0 n0.
Constraint k0 <= max(m0, n0).
Constraint k0 <= m0, m0 <= n0.
Print Universes Subgraph (k0 m0 n0).

(* The new clause is not on the premise itself: c1 <= max(p1, q1) and p1 <= z1, then z1 <= q1
   makes p1 <= q1, found going down from z1 *)
Universes c1 p1 q1 z1.
Constraint c1 <= max(p1, q1).
Constraint p1 <= z1.
Constraint z1 <= q1.
Print Universes Subgraph (c1 p1 q1 z1).

(* Through a longer chain, with many universes below z2 and few above: the clause is found going
   up from z2, through its other premise q2 *)
Universes c2 p2 q2 y2 z2 a2 b2 r2.
Constraint c2 <= max(p2, q2).
Constraint p2 <= y2, y2 <= z2.
Constraint a2 <= p2, b2 <= p2, r2 <= a2.
Constraint z2 <= q2.
Print Universes Subgraph (c2 p2 q2 y2 z2).

(* After a merge: p3 = r3 with r3 <= q3 makes p3 <= q3 *)
Universes c3 p3 q3 r3.
Constraint c3 <= max(p3, q3).
Constraint r3 <= q3.
Constraint p3 = r3.
Print Universes Subgraph (c3 p3 q3 r3).

(* After a merge of the conclusion: c4 = w4 with p4 <= w4 makes p4 <= c4, below c4 + 1 *)
Universes c4 p4 q4 w4.
Constraint c4 < max(p4, q4).
Constraint p4 <= w4.
Constraint c4 = w4.
Print Universes Subgraph (c4 p4 q4 w4).

(* Two clauses below the new one: with p5 <= q5, c5 <= max(p5, q5) is c5 <= q5, and then
   e5 <= max(c5, q5+1) is e5 <= q5+1 *)
Universes c5 e5 p5 q5.
Constraint e5 <= max(c5, q5+1).
Constraint c5 <= max(p5, q5).
Constraint p5 <= q5.
Print Universes Subgraph (c5 e5 p5 q5).
