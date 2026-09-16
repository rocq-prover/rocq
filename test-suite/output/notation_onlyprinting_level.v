(* #12465, #12589: a declaration with no parsing rule has no grammar to agree
   with, so its level need not match the recorded one.

   Shaped like VST's floyd/Clightnotations.v over ssreflect's "_ == _". *)
Declare Scope test_bool_scope.
Notation "x == y" := (Nat.eqb x y) (at level 70, no associativity) : test_bool_scope.
Declare Scope test_expr_scope.
Notation "a1 == a2" := (andb a1 a2)
  (only printing, a2 at level 16, left associativity, at level 17,
   format "'[' a1  ==  a2 ']'") : test_expr_scope.

(* Parsing still uses the level 70 rule. *)
Open Scope test_bool_scope.
Check (0 == 1 + 1).

(* Printing uses the "only printing" rule at its own level 17, which is left
   associative, so only the right argument gets parentheses. *)
Open Scope test_expr_scope.
Check (andb (andb true false) (andb true false)).

(* The declared level reaches the printing rule only through a format.  Without
   one, "<<" keeps the level 70 rule, which has no associativity. *)
Declare Scope test_bool_scope2.
Notation "x << y" := (Nat.leb x y) (at level 70, no associativity) : test_bool_scope2.
Declare Scope test_expr_scope2.
Notation "a1 << a2" := (andb a1 a2)
  (only printing, a2 at level 16, left associativity, at level 17) : test_expr_scope2.
Open Scope test_expr_scope2.
Check (andb (andb true false) (andb true false)).

(* Extra spaces are an implicit format, and that is enough: ">>" prints at the
   declared level 17 with no "format" modifier given. *)
Declare Scope test_bool_scope3.
Notation "x >> y" := (Nat.leb x y) (at level 70, no associativity) : test_bool_scope3.
Declare Scope test_expr_scope3.
Notation "a1  >>  a2" := (andb a1 a2)
  (only printing, a2 at level 16, left associativity, at level 17) : test_expr_scope3.
Open Scope test_expr_scope3.
Check (andb (andb true false) (andb true false)).

(* The argument levels reach printing with no format at all, through the
   coercions between entries they make available.  The parsing rule takes its
   right operand at level 70 and a right-nested term prints bare.  The "only
   printing" one takes it at level 0 and the same term gains parentheses. *)
Declare Custom Entry test_entry.
Notation "[ x ]" := x (in custom test_entry at level 0, x constr at level 0).
Notation "( x )" := x (in custom test_entry at level 0, x custom test_entry at level 200).
Notation "<{ e }>" := e (e custom test_entry at level 200).
Notation "x ** y" := (Nat.add x y) (in custom test_entry at level 70, y at level 70).
Check (Nat.add 1 (Nat.add 2 3)).
Declare Scope test_custom_scope.
Notation "x ** y" := (Nat.mul x y)
  (in custom test_entry at level 70, y at level 0, only printing) : test_custom_scope.
Open Scope test_custom_scope.
Check (Nat.mul 1 (Nat.mul 2 3)).
(* The parenthesised form reads back as the same term. *)
Check (<{ [1] ** ([2] ** [3]) }>).

(* A "Reserved Notation" declared "only printing" with a format takes over the
   printing rule of the whole notation string.  So "<?>", parsed at level 17
   left associative, prints at level 70 and gains parentheses.  They are
   redundant for the parsing rule, but the output still reads back. *)
Reserved Notation "x <?> y" (at level 17, left associativity, y at level 16).
Notation "x <?> y" := (Nat.mul x y) : nat_scope.
Check (Nat.mul (Nat.mul 5 2) 1).
Reserved Notation "x <?> y" (only printing, at level 70, no associativity,
                             format "'[' x  <?>  y ']'").
Check (Nat.mul (Nat.mul 5 2) 1).
Check ((5 <?> 2) <?> 1).

(* Without a format there is no rule to take over, so the same shape leaves
   level 17 in place and "<!>" prints without parentheses. *)
Reserved Notation "x <!> y" (at level 17, left associativity, y at level 16).
Notation "x <!> y" := (Nat.mul x y) : nat_scope.
Reserved Notation "x <!> y" (only printing, at level 70, no associativity).
Check (Nat.mul (Nat.mul 5 2) 1).

(* A declaration with no modifier at all, on a string that so far had only
   "only printing" rules, recovers the recorded level, so it reports only when
   Import replays it.  Both declarations below warn at the Import line. *)
Module Recovered.
  Declare Scope test_rec_scope.
  Notation "x ## y" := (andb x y)
    (only printing, at level 17, left associativity, y at level 16) : test_rec_scope.
  Declare Scope test_rec_scope2.
  Notation "x ## y" := (orb x y) : test_rec_scope2.
End Recovered.
Declare Scope test_rec_scope3.
Notation "x ## y" := (Nat.eqb x y) (at level 70, no associativity) : test_rec_scope3.
Import Recovered.

(* In the other order the later declaration brings the parsing rule, and the
   recorded level stays put.  The warning says which case it is. *)
Declare Scope test_mirror_scope.
Notation "x @@ y" := (andb x y)
  (only printing, at level 17, left associativity, y at level 16) : test_mirror_scope.
Declare Scope test_mirror_scope2.
Notation "x @@ y" := (orb x y) (at level 70, no associativity) : test_mirror_scope2.

(* Two parsing rules at incompatible levels are still an error, including when
   the second is "only parsing". *)
Declare Scope test_a_scope.
Notation "x <=> y" := (Nat.eqb x y) (at level 70, no associativity) : test_a_scope.
Declare Scope test_b_scope.
Fail Notation "x <=> y" := (andb x y)
  (y at level 16, left associativity, at level 17) : test_b_scope.
Fail Notation "x <=> y" := (andb x y)
  (only parsing, y at level 16, left associativity, at level 17) : test_b_scope.

(* An older gap, untouched here: once a rule-less declaration has recorded the
   level, no grammar is recorded for the string, so further parsing rules at
   incompatible levels only warn. *)
Declare Scope test_gap_scope.
Notation "x <%> y" := (andb x y)
  (only printing, at level 17, left associativity, y at level 16) : test_gap_scope.
Declare Scope test_gap_scope2.
Notation "x <%> y" := (orb x y) (at level 70, no associativity) : test_gap_scope2.
Declare Scope test_gap_scope3.
Notation "x <%> y" := (Nat.eqb x y) (at level 80, no associativity) : test_gap_scope3.
