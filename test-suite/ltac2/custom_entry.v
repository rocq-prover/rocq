Require Import Ltac2.Ltac2.

Ltac2 Custom Entry mycustom.

Ltac2 Notation "mycustom:(" x(mycustom) ")" := x.

(* NB this test declares level not in order deliberately *)

(* custom entries get autodeclared as RIGHTA, but we can still do left
   associative notations *)
Ltac2 Notation x(self) "+" y(next) : mycustom(2) := (x, y).

(* we can also do right associative notations *)
Ltac2 Notation x(self) "-" y(self) : mycustom(1) := (x, y).

(* put back atomic tactics in mycustom *)
Ltac2 Notation x(tactic(0)) : mycustom(0) := x.

Ltac2 Eval (mycustom:("" + 1 + true) : (string * int) * bool).
Ltac2 Eval (mycustom:("" - 1 - true) : string * (int * bool)).

(* - (level 1) binds stronger than + (level 2) *)
Ltac2 Eval (mycustom:("" + 1 - true) : string * (int * bool)).
Ltac2 Eval (mycustom:("" - 1 + true) : (string * int) * bool).


Ltac2 Custom Entry math.

(* unspecified level means highest possible level *)
Ltac2 Notation "math:(" x(math) ")" : 0 := x.
Ltac2 Notation "(" x(math) ")" : math(0) := x.

(* next on the right: these are all left associative *)
Ltac2 Notation x(self) "<" y(next) : math(70) := (Int.lt x y).
Ltac2 Notation x(self) "<=" y(next) : math(70) := (Int.le x y).
Ltac2 Notation x(self) "=" y(next) : math(70) := (Int.equal x y).
Ltac2 Notation x(self) "+" y(next) : math(50) := (Int.add x y).
Ltac2 Notation x(self) "-" y(next) : math(50) := (Int.sub x y).
Ltac2 Notation x(self) "*" y(next) : math(40) := (Int.mul x y).
Ltac2 Notation x(self) "/" y(next) : math(40) := (Int.div x y).

Ltac2 Notation "-" x(self) : math(35) := (Int.neg x).

(* ltac2_atom and int aren't available as a custom entry (should it
   be?) so we need to use tactic(0) to parse ltac2 references and
   literal ints

   Since tactic(0) includes parenthesized tactics we can't insert it
   directly like we did for mycustom, so instead use the ' prefix *)
Ltac2 Notation "'" x(tactic(0)) : math(0) := x.

Ltac2 Eval Control.assert_true (Int.equal 14 math:('2 + '3 * '4)).
Ltac2 Eval Control.assert_true (Int.equal 20 math:(('2 + '3) * '4)).

Ltac2 Eval Control.assert_true math:('2 < '2 + '1).
Ltac2 Eval Control.assert_false math:('2 < '2 - '1).

Ltac2 Eval Control.assert_true math:('3 = '0 - - '3).
Ltac2 Eval Control.assert_true math:('2 = '3 * '2 / '3).
Ltac2 Eval Control.assert_true math:('0 = '3 * ('2 / '3)).

Ltac2 Eval Control.assert_true math:(- - '1 = - - - - '1).

(* TODO undeclared level leads to anomaly *)
Ltac2 Notation "bad" x(mycustom(3)) : mycustom(2) := x.
Ltac2 Eval mycustom:(bad 0).
