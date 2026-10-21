(* Soundness and completeness of loop-checking on universe constraints.

   Universes are natural numbers, Set is 0 and [n] is Set+n. A global
   universe declared with [Universe] is strictly above Set. Constraints
   [l <= r], [l < r] and [l = r] relate universes [max(u1+k1, ..., un+kn)].

   - Completeness: [Check Constraint c] must succeed for every [c] entailed by
     the declared constraints.
   - Soundness: [Fail Check Constraint c] for constraints that do not follow,
     each with a counter-model in a comment, and [Fail Constraint] for
     constraints that would make the graph inconsistent.

   Each block uses fresh universes, so that the graph only grows. *)

Unset Universe Polymorphism.

(** * Basics *)

Universes a1 a2.
Constraint a1 < a2.

Check Constraint a1 <= a2, a1 < a2, a1+1 <= a2.
(* Lower bounds: 1 <= a1 as a1 is global, hence 2 <= a2 *)
Check Constraint 1 <= a1, Set < a1, 2 <= a2, Set+2 <= a2.
Check Constraint max(a1, 1) <= a2, max(a1+1, 2) <= a2.
Fail Check Constraint a2 <= a1.       (* a1 = 1, a2 = 2 *)
Fail Check Constraint a1+2 <= a2.     (* a1 = 1, a2 = 2 *)
Fail Check Constraint a1 = a2.
Fail Check Constraint 3 <= a2.        (* a1 = 1, a2 = 2 *)
Fail Check Constraint 2 <= a1.        (* a1 = 1 *)

(** * Chains and lower bounds through intermediate universes *)

(* A small graph: Set, b0 ... b4. Lower bounds on b4 are derived through all
   the other universes, the propagation updating all of them. *)
Universes b0 b1 b2 b3 b4.
Constraint b0 < b1, b1 < b2, b2 < b3, b3 < b4.

Check Constraint b0+4 <= b4, b1+3 <= b4, b0+2 <= b2.
Check Constraint 5 <= b4, 4 <= b3, 3 <= b2.
Check Constraint max(b0+4, b1+3, b2+2, b3+1, 5) <= b4.
Fail Check Constraint b0+5 <= b4.     (* bi = i+1 *)
Fail Check Constraint 6 <= b4.        (* bi = i+1 *)
Fail Check Constraint b4 <= b3.
Fail Check Constraint b1+4 <= b4.     (* bi = i+1 *)

(* Non-strict steps and shifts *)
Universes c0 c1 c2 c3.
Constraint c0+2 <= c1, c1 <= c2, c2+3 <= c3.
Check Constraint c0+5 <= c3, c1+3 <= c3, c0 < c3.
Check Constraint 6 <= c3, 3 <= c1, 3 <= c2.
Fail Check Constraint c0+6 <= c3.     (* c0 = 1, c1 = c2 = 3, c3 = 6 *)
Fail Check Constraint c1 < c2.        (* c1 = c2 *)
Fail Check Constraint 7 <= c3.        (* c0 = 1, c1 = c2 = 3, c3 = 6 *)

(** * Cycles of non-strict constraints are equalities *)

Universes d1 d2 d3 d4.
Constraint d1 <= d2, d2 <= d3, d3 <= d1, d3 < d4.
Check Constraint d1 = d2, d2 = d3, d1 = d3.
Check Constraint d1 < d4, d2+1 <= d4, max(d1, d2, d3) < d4.
Fail Check Constraint d1 < d2.
Fail Check Constraint d4 <= d1.
Fail Check Constraint d1+2 <= d4.     (* d1 = d2 = d3 = 1, d4 = 2 *)

(* A cycle with a slack clause s2 <= s4+1: merging the cycle must not equate s2 and s4+1 *)
Universes s1 s2 s3 s4.
Constraint s1 <= s2, s2 <= s3, s3 <= s4, s2 <= s4+1, s4 <= s1.
Check Constraint s1 = s2, s2 = s3, s3 = s4, s2 <= s4+1.
Fail Check Constraint s2 = s4+1.
Fail Check Constraint s4+1 <= s2.     (* s1 = s2 = s3 = s4 = 1 *)

(* Equality through max: max(e1, e2) <= e3 and e3 <= e1 give e1 = e3 and e2 <= e1 *)
Universes e1 e2 e3.
Constraint max(e1, e2) <= e3, e3 <= e1.
Check Constraint e1 = e3, e2 <= e1, max(e1, e2) = e1, max(e2, e3) = e1.
Fail Check Constraint e1 = e2.        (* e2 = 1, e1 = e3 = 2 *)
Fail Check Constraint e2 = e3.        (* e2 = 1, e1 = e3 = 2 *)
Fail Check Constraint e1 <= e2.       (* e2 = 1, e1 = e3 = 2 *)

(** * Max on the left: a conjunction *)

Universes f1 f2 f3.
Constraint max(f1, f2+1) <= f3.
Check Constraint f1 <= f3, f2 < f3, max(f1, f2) <= f3, max(f1, f2+1, 2) <= f3.
Fail Check Constraint f1 < f3.        (* f1 = f3 = 2, f2 = 1 *)
Fail Check Constraint f2+2 <= f3.     (* f1 = 1, f2 = 1, f3 = 2 *)
Fail Check Constraint f3 <= max(f1, f2). (* f1 = f2 = 1, f3 = 2 *)

(** * Max on the right: a disjunction *)

Universes g1 g2 g3 g4.
Constraint g1 <= max(g2, g3).
Check Constraint g1 <= max(g2, g3), g1 <= max(g3, g2), g1 <= max(g2, g3, g4).
Check Constraint max(g1, g2) <= max(g2, g3), max(g1, g2, g3) <= max(g2, g3).
Check Constraint g1 <= max(g2+1, g3), g1 <= max(g2, g3+2).
Fail Check Constraint g1 <= g2.       (* g1 = g3 = 2, g2 = 1 *)
Fail Check Constraint g1 <= g3.       (* g1 = g2 = 2, g3 = 1 *)
Fail Check Constraint g1 < max(g2, g3). (* g1 = g2 = g3 = 1 *)
Fail Check Constraint g1 <= max(g2, g4). (* g1 = g3 = 2, g2 = g4 = 1 *)

(* Case analysis: both cases lead to h4 *)
Universes h1 h2 h3 h4 h5.
Constraint h1 <= max(h2, h3), h2 <= h4, h3 < h4, h4 < h5.
Check Constraint h1 <= h4, h1 < h5, h1+1 <= h5, max(h1, h2, h3) <= h4.
Fail Check Constraint h1 < h4.        (* h1 = h2 = h4 = 2, h3 = 1, h5 = 3 *)
Fail Check Constraint h1+2 <= h5.     (* h1 = h2 = h4 = 2, h3 = 1, h5 = 3 *)
Fail Check Constraint h2 < h4.        (* h1 = h2 = h4 = 2, h3 = 1, h5 = 3 *)

(* Case analysis with shifts: i1+1 <= max(i2, i3+2) gives i1 <= max(i2, i3+1) *)
Universes i1 i2 i3.
Constraint i1+1 <= max(i2, i3+2).
Check Constraint i1 <= max(i2, i3+1), i1 <= max(i2+5, i3+1), i1+1 <= max(i2, i3+2).
Fail Check Constraint i1 <= max(i2, i3).   (* i2 = 1, i3 = 1, i1 = 2 *)
Fail Check Constraint i1+1 <= max(i2, i3+1). (* i2 = 1, i3 = 1, i1 = 2 *)

(* The cases distribute: j1 <= max(j2, j3), j2 <= j4, j3 <= j5 gives j1 <= max(j4, j5) *)
Universes j1 j2 j3 j4 j5.
Constraint j1 <= max(j2, j3), j2 <= j4, j3 <= j5.
Check Constraint j1 <= max(j4, j5), j1 <= max(j2, j5), j1 <= max(j4, j3).
Fail Check Constraint j1 <= j4.       (* j1 = j3 = j5 = 2, j2 = j4 = 1 *)
Fail Check Constraint j1 <= j5.       (* j1 = j2 = j4 = 2, j3 = j5 = 1 *)
Fail Check Constraint j1 <= max(j2, j4). (* j1 = j3 = j5 = 2, j2 = j4 = 1 *)

(** * Strict self-references *)

(* k1 < max(k1, k2) can only hold through k2 *)
Universes k1 k2.
Constraint k1 < max(k1, k2).
Check Constraint k1 < k2, k1+1 <= k2, 2 <= k2.
Fail Check Constraint k1+2 <= k2.     (* k1 = 1, k2 = 2 *)

(* l1+2 <= max(l1+1, l2) can only hold through l2 *)
Universes l1 l2.
Constraint l1+2 <= max(l1+1, l2).
Check Constraint l1+2 <= l2, 3 <= l2.
Fail Check Constraint l1+3 <= l2.     (* l1 = 1, l2 = 3 *)

(** * Inconsistent constraints are rejected *)

Universes m1 m2 m3.
Constraint m1 <= m2.
Fail Constraint m2 < m1.
Fail Constraint m1 < m1.
Fail Constraint m1+1 <= max(m1, m1).
Fail Constraint max(m3, m1) < m3.
Fail Constraint m2 < m3, m3 < m1.
Fail Constraint m1 = m2+1.
Fail Constraint m1 < Set.
Fail Constraint m1 <= 0.               (* m1 is global, so 1 <= m1 *)
(* The failed attempts did not change the graph *)
Check Constraint m1 <= m2.
Fail Check Constraint m2 <= m1.
Fail Check Constraint m3 <= m1.
Fail Check Constraint m1 <= m3.

(** * Shifted equalities *)

Universes n1 n2 n3.
Constraint n1+1 = n2, n2+2 = n3.
Check Constraint n1 < n2, n2 <= n1+1, n1+3 = n3, n3 <= n1+3, 4 <= n3.
Check Constraint max(n1+3, n2+2) = n3.
Fail Check Constraint n2 <= n1.
Fail Check Constraint n3 <= n1+2.
Fail Check Constraint n1+4 <= n3.
Fail Check Constraint 5 <= n3.         (* n1 = 1, n2 = 2, n3 = 4 *)

(** * Consistent constraints on small graphs *)

(* Updating all the universes of a small graph is not a loop: enforcing these constraints in
   this order, or restricting them to print the subgraph, used to fail *)
Universes w0 w1 w2 w3 w4.
Constraint w3+1 <= w2, w2+1 <= w0+1, w2+1 <= w4, w4+1 <= max(w2+1, w0),
  w3 <= max(w1, w4), w0 <= w1, w3 <= max(w2, w4).
Print Universes Subgraph (w0 w1 w2 w3 w4).
(* w4+1 <= max(w2+1, w0) with w2 < w4 gives w4 < w0 *)
Check Constraint w3+2 <= w4, w2 <= w0, w4 < w0.
Fail Check Constraint w4+2 <= w0.     (* w3 = 1, w2 = 2, w4 = 3, w0 = w1 = 4 *)

(* Checking z0+1 <= z3 used not to terminate, when the value of Set is large compared to the
   ones of the z universes, as with the lower bound of zc *)
Universes zc z0 z1 z2 z3.
Constraint 7 <= zc.
Constraint z2+1 <= z1, z2 <= z3, z2 <= z0, z1+1 <= max(z2, z0), z0+1 <= max(z1, z3),
  z2 <= max(z1, z0).
(* z1 < max(z2, z0) with z2 < z1 gives z1 < z0, then z0 < max(z1, z3) gives z0 < z3 *)
Check Constraint z0+1 <= z3, z2+2 <= z0.
Fail Check Constraint z0+2 <= z3.     (* z2 = 1, z1 = 2, z0 = 3, z3 = 4 *)

(** * Stress: long chains *)

(* p0 < p1 < ... < p29 *)
Universes p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19
  p20 p21 p22 p23 p24 p25 p26 p27 p28 p29.
Constraint p0 < p1, p1 < p2, p2 < p3, p3 < p4, p4 < p5, p5 < p6, p6 < p7, p7 < p8, p8 < p9,
  p9 < p10, p10 < p11, p11 < p12, p12 < p13, p13 < p14, p14 < p15, p15 < p16, p16 < p17,
  p17 < p18, p18 < p19, p19 < p20, p20 < p21, p21 < p22, p22 < p23, p23 < p24, p24 < p25,
  p25 < p26, p26 < p27, p27 < p28, p28 < p29.
Check Constraint p0+29 <= p29, p10+19 <= p29, 30 <= p29, 15 <= p14.
Check Constraint max(p0+29, p1+28, p15+14, p28+1, 30) <= p29.
Fail Check Constraint p0+30 <= p29.   (* pi = i+1 *)
Fail Check Constraint 31 <= p29.      (* pi = i+1 *)
Fail Check Constraint p29 <= p28.

(* A chain closed by an equality: all of q0 ... q9 are equal *)
Universes q0 q1 q2 q3 q4 q5 q6 q7 q8 q9.
Constraint q0 <= q1, q1 <= q2, q2 <= q3, q3 <= q4, q4 <= q5, q5 <= q6, q6 <= q7,
  q7 <= q8, q8 <= q9, q9 <= q0.
Check Constraint q0 = q9, q3 = q7, max(q0, q1, q2, q3, q4, q5, q6, q7, q8, q9) = q5.
Fail Check Constraint q0 < q9.

(* Each universe is above the max of the two previous ones:
   r(i+2) >= max(r i, r(i+1)) + 1, so r(n) >= r1 + n - 1 and r(n) >= n + 1 *)
Universes r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15.
Constraint max(r0, r1) < r2, max(r1, r2) < r3, max(r2, r3) < r4, max(r3, r4) < r5,
  max(r4, r5) < r6, max(r5, r6) < r7, max(r6, r7) < r8, max(r7, r8) < r9,
  max(r8, r9) < r10, max(r9, r10) < r11, max(r10, r11) < r12, max(r11, r12) < r13,
  max(r12, r13) < r14, max(r13, r14) < r15.
Check Constraint r1+14 <= r15, r0+14 <= r15, 15 <= r15, max(r0+14, r1+14) <= r15.
Fail Check Constraint r1+15 <= r15.   (* r0 = r1 = 1, ri = i for i >= 2 *)
Fail Check Constraint 16 <= r15.      (* r0 = r1 = 1, ri = i for i >= 2 *)
Fail Check Constraint r0+15 <= r15.   (* r0 = r1 = 1, ri = i for i >= 2 *)

(* A wide disjunction: s <= max(x1, ..., x8) and every xi < y gives s < y *)
Universes s x1 x2 x3 x4 x5 x6 x7 x8 y.
Constraint s <= max(x1, x2, x3, x4, x5, x6, x7, x8),
  x1 < y, x2 < y, x3 < y, x4 < y, x5 < y, x6 < y, x7 < y, x8 < y.
Check Constraint s < y, s+1 <= y, max(s, x1, x8) < y.
Fail Check Constraint s+2 <= y.       (* s = x8 = 1, other xi = 1, y = 2 *)
Fail Check Constraint s <= max(x1, x2, x3, x4, x5, x6, x7). (* s = x8 = 2, other xi = 1, y = 3 *)
Fail Check Constraint s <= x1.        (* s = x8 = 2, other xi = 1, y = 3 *)

(* A diamond lattice: t00 at the bottom, t33 at the top, each step strict *)
Universes t00 t01 t02 t03 t10 t11 t12 t13 t20 t21 t22 t23 t30 t31 t32 t33.
Constraint
  t00 < t01, t01 < t02, t02 < t03, t10 < t11, t11 < t12, t12 < t13,
  t20 < t21, t21 < t22, t22 < t23, t30 < t31, t31 < t32, t32 < t33,
  t00 < t10, t10 < t20, t20 < t30, t01 < t11, t11 < t21, t21 < t31,
  t02 < t12, t12 < t22, t22 < t32, t03 < t13, t13 < t23, t23 < t33.
Check Constraint t00+6 <= t33, t03+3 <= t33, t30+3 <= t33, t11+4 <= t33, 7 <= t33.
Check Constraint max(t03+3, t30+3) <= t33, max(t12, t21) < t33.
Fail Check Constraint t00+7 <= t33.   (* tij = i+j+1 *)
Fail Check Constraint t03 <= t30.     (* tij = i+2j+1 *)
Fail Check Constraint t30 <= t03.     (* tij = 2i+j+1 *)
Fail Check Constraint 8 <= t33.       (* tij = i+j+1 *)

(** * Polymorphic section universes (local graph) *)

Section S.
  #[universes(polymorphic)] Universes u1 u2 u3.
  #[universes(polymorphic)] Constraint u1 < u2, u2 <= max(u1, u3).
  (* u2 <= u1 is impossible, so u2 <= u3 *)
  Check Constraint u2 <= u3, u1 < u3, u1+1 <= u3.
  Fail Check Constraint u3 <= u2.     (* u1 = 1, u2 = 2, u3 = 3 *)
  Fail Check Constraint u1+2 <= u3.   (* u1 = 1, u2 = u3 = 2 *)
End S.
