(* #12465: a declaration that adds no parsing rule has no grammar to agree
   with, so its level need not match the one recorded for the notation string.
   The notation-incompatible-level warning reports the mismatch. *)

Declare Scope test_bool_scope.
Notation "x == y" := (Nat.eqb x y) (at level 70, no associativity) : test_bool_scope.

(* Shaped like VST's floyd/Clightnotations.v. *)
Declare Scope test_expr_scope.
Notation "a1 == a2" := (andb a1 a2)
  (only printing, a2 at level 16, left associativity, at level 17,
   format "'[' a1  ==  a2 ']'") : test_expr_scope.

(* Parsing still uses the level 70 rule. *)
Open Scope test_bool_scope.
Check (0 == 1).
Check (0 == 1 + 1).

(* Printing uses the "only printing" rule at its own level 17.  That rule is
   left associative, so the left argument needs no parentheses and the right
   one does. *)
Open Scope test_expr_scope.
Check (andb (andb true false) (andb true false)).

(* The declared level reaches the printing rule only when the declaration
   comes with a format.  Without one the existing rule is kept, level and all.
   So "<<" below still prints at level 70.  That level has no associativity, so
   it parenthesizes both of its arguments. *)
Declare Scope test_bool_scope2.
Notation "x << y" := (Nat.leb x y) (at level 70, no associativity) : test_bool_scope2.
Declare Scope test_expr_scope2.
Notation "a1 << a2" := (andb a1 a2)
  (only printing, a2 at level 16, left associativity, at level 17) : test_expr_scope2.
Open Scope test_expr_scope2.
Check (andb (andb true false) (andb true false)).

(* Extra spaces in the notation string count as a format, an implicit one, and
   that is enough.  ">>" below prints at the declared level 17, left
   associatively, with no "format" modifier given. *)
Declare Scope test_bool_scope3.
Notation "x >> y" := (Nat.leb x y) (at level 70, no associativity) : test_bool_scope3.
Declare Scope test_expr_scope3.
Notation "a1  >>  a2" := (andb a1 a2)
  (only printing, a2 at level 16, left associativity, at level 17) : test_expr_scope3.
Open Scope test_expr_scope3.
Check (andb (andb true false) (andb true false)).

(* The other way a declaration's levels reach printing needs no format at all.
   The argument levels go into the interpretation, where they decide which
   coercions between entries are available.  In a custom entry that shows up
   directly.  The parsing rule below takes a right operand at level 70, so a
   right-nested term prints without parentheses.  The "only printing"
   declaration puts its right operand at level 0, so the same term gains them.
   No "format" modifier is involved. *)
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
(* The parenthesised form reads back as the same term, with no tolerance. *)
Check (<{ [1] ** ([2] ** [3]) }>).

(* A "Reserved Notation" declared "only printing" with a format gets no
   printing rule of its own.  It takes over the one shared by the whole
   notation string.  So giving it its own level also changes how the parsing
   notation for that string prints.  Here "<?>" is parsed at level 17, left
   associatively, and printed at level 70, which has no associativity.  The
   printed form gains parentheses.  They are redundant for the parsing rule but
   harmless, and the output reads back as the same term. *)
Reserved Notation "x <?> y" (at level 17, left associativity, y at level 16).
Notation "x <?> y" := (Nat.mul x y) : nat_scope.
Check (Nat.mul (Nat.mul 5 2) 1).
Reserved Notation "x <?> y" (only printing, at level 70, no associativity,
                             format "'[' x  <?>  y ']'").
Check (Nat.mul (Nat.mul 5 2) 1).
Check ((5 <?> 2) <?> 1).

(* The warning is not tied to the "only printing" modifier, which is why it
   does not name it.  A declaration with no modifier at all, on a string that
   so far had only "only printing" rules, recovers the recorded level.  It
   reports only when Import replays it against a level recorded since.  Both
   declarations below warn at the Import line, not where they are written. *)
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

(* The mismatch is reported in the other order too.  There the later
   declaration brings the parsing rule and the recorded level stays put.  The
   closing sentence of the warning says so. *)
Declare Scope test_mirror_scope.
Notation "x @@ y" := (andb x y)
  (only printing, at level 17, left associativity, y at level 16) : test_mirror_scope.
Declare Scope test_mirror_scope2.
Notation "x @@ y" := (orb x y) (at level 70, no associativity) : test_mirror_scope2.

(* Two parsing rules for the same notation string at incompatible levels are
   still an error.  The message is pinned here, not just the failure. *)
Declare Scope test_a_scope.
Notation "x <=> y" := (Nat.eqb x y) (at level 70, no associativity) : test_a_scope.
Declare Scope test_b_scope.
Fail Notation "x <=> y" := (andb x y)
  (y at level 16, left associativity, at level 17) : test_b_scope.
(* ... and also when the second one is declared "only parsing". *)
Fail Notation "x <=> y" := (andb x y)
  (only parsing, y at level 16, left associativity, at level 17) : test_b_scope.
