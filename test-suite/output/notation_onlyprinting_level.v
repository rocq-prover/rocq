Declare Scope test_bool_scope.
Notation "x == y" := (Nat.eqb x y) (at level 70, no associativity) : test_bool_scope.
Declare Scope test_expr_scope.
Notation "a1 == a2" := (andb a1 a2)
  (only printing, a2 at level 16, left associativity, at level 17,
   format "'[' a1  ==  a2 ']'") : test_expr_scope.

(* Parsing still uses level 70. *)
Open Scope test_bool_scope.
Check (0 == 1 + 1).

(* Printing uses the left-associative rule at level 17. *)
Open Scope test_expr_scope.
Check (andb (andb true false) (andb true false)).

(* Without a format, "<<" keeps the level 70 printing rule. *)
Declare Scope test_bool_scope2.
Notation "x << y" := (Nat.leb x y) (at level 70, no associativity) : test_bool_scope2.
Declare Scope test_expr_scope2.
Notation "a1 << a2" := (andb a1 a2)
  (only printing, a2 at level 16, left associativity, at level 17) : test_expr_scope2.
Open Scope test_expr_scope2.
Check (andb (andb true false) (andb true false)).

(* Extra spaces give ">>" an implicit format at level 17. *)
Declare Scope test_bool_scope3.
Notation "x >> y" := (Nat.leb x y) (at level 70, no associativity) : test_bool_scope3.
Declare Scope test_expr_scope3.
Notation "a1  >>  a2" := (andb a1 a2)
  (only printing, a2 at level 16, left associativity, at level 17) : test_expr_scope3.
Open Scope test_expr_scope3.
Check (andb (andb true false) (andb true false)).

(* Argument levels affect printing even without a format. *)
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
(* The parenthesized form reads back as the same term. *)
Check (<{ [1] ** ([2] ** [3]) }>).

(* A formatted "only printing" reservation replaces the shared printing rule. *)
Reserved Notation "x <?> y" (at level 17, left associativity, y at level 16).
Notation "x <?> y" := (Nat.mul x y) : nat_scope.
Check (Nat.mul (Nat.mul 5 2) 1).
Reserved Notation "x <?> y" (only printing, at level 70, no associativity,
                             format "'[' x  <?>  y ']'").
Check (Nat.mul (Nat.mul 5 2) 1).
Check ((5 <?> 2) <?> 1).

(* Without a format, the shared rule stays at level 17. *)
Reserved Notation "x <!> y" (at level 17, left associativity, y at level 16).
Notation "x <!> y" := (Nat.mul x y) : nat_scope.
Reserved Notation "x <!> y" (only printing, at level 70, no associativity).
Check (Nat.mul (Nat.mul 5 2) 1).

(* Import reports recovered declarations that lack a parsing rule. *)
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

(* The reverse declaration order warns too. *)
Declare Scope test_mirror_scope.
Notation "x @@ y" := (andb x y)
  (only printing, at level 17, left associativity, y at level 16) : test_mirror_scope.
Declare Scope test_mirror_scope2.
Notation "x @@ y" := (orb x y)
  (at level 70, y at next level, no associativity) : test_mirror_scope2.

(* Two incompatible parsing rules remain an error. *)
Declare Scope test_a_scope.
Notation "x <=> y" := (Nat.eqb x y) (at level 70, no associativity) : test_a_scope.
Declare Scope test_b_scope.
Fail Notation "x <=> y" := (andb x y)
  (y at level 16, left associativity, at level 17) : test_b_scope.
Fail Notation "x <=> y" := (andb x y)
  (only parsing, y at level 16, left associativity, at level 17) : test_b_scope.
