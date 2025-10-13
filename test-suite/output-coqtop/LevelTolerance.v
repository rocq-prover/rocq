Set Warnings "+level-tolerance".
Set Warnings "-closed-notation-not-level-0".
Set Warnings "-level-0-notation-not-closed".
Set Warnings "-postfix-notation-not-level-1".

Inductive T := E : T | F : T -> T | G : T -> T -> T.
Inductive Parsing {A} := Accept (_ : nat) (_ : A) | Reject (_ : nat) (_ : A).

Declare Custom Entry expr.

Notation "x 'op22' y" := (G x y) (in custom expr at level 3, only parsing, no associativity).
Notation "x 'op12' y" := (G x y) (in custom expr at level 2, only parsing, right associativity).
Notation "x 'op10' y" := (G x y) (in custom expr at level 1, only parsing, left associativity).

Notation "[3 e ]" := e (e custom expr at level 3, only parsing).
Notation "[2 e ]" := e (e custom expr at level 2, only parsing).
Notation "[1 e ]" := e (e custom expr at level 1, only parsing).
Notation "[0 e ]" := e (e custom expr at level 0, only parsing).

Notation "'atom3'" := E (in custom expr at level 3, only parsing).
Notation "'atom2'" := E (in custom expr at level 2, only parsing).
Notation "'atom1'" := E (in custom expr at level 1, only parsing).
Notation "'atom0'" := E (in custom expr at level 0, only parsing).

Notation "'pre22' x" := (F x) (in custom expr at level 2, x at level 2, only parsing).
Notation "'pre21' x" := (F x) (in custom expr at level 2, x at next level, only parsing).
Notation "'pre11' x" := (F x) (in custom expr at level 1, x at level 1, only parsing).
Notation "'pre10' x" := (F x) (in custom expr at level 1, x at next level, only parsing).
Notation "'pre00' x" := (F x) (in custom expr at level 0, x at level 0, only parsing).
Notation "'pre0x' x" := (F x) (in custom expr at level 0, x at next level, only parsing).

Notation "x 'post12'" := (F x) (in custom expr at level 2, only parsing).
Notation "x 'post11'" := (F x) (in custom expr at level 1, only parsing).

Print Custom Grammar expr.

(* The following sed script prints the first line with a wrong result:

     sed -En '/Accept/{/^(Rocq < )+Accept/!bf};/Reject/{/^> Check Reject/!bf};b;:f;p;q1' \
       test-suite/output-coqtop/LevelTolerance.out

   The script checks that:
   - Each line containing "Reject" starts with "> Check Reject"
   - Each line containing "Accept" starts with one or more "Rocq < " followed by "Accept"

   In case of failure, it prints the line containing "Reject" or "Accept". *)

Check Reject 10 [2 atom3 ].
Check Accept 11 [2 atom2 ].
Check Reject 12 [1 atom2 ].
Check Accept 13 [1 atom1 ].

Check Reject 20 [2 pre22 atom3 ].
Check Accept 21 [2 pre22 atom2 ].
Check Reject 22 [1 pre22 atom2 ].

Check Reject 30 [2 pre21 atom2 ].
Check Accept 31 [2 pre21 atom1 ].
Check Reject 32 [1 pre21 atom1 ].

Check Reject 40 [2 pre11 atom2 ].
Check Reject 41 [1 pre11 atom2 ].
Check Accept 42 [1 pre11 atom1 ].
Check Reject 43 [0 pre11 atom1 ].

Check Reject 50 [1 pre10 atom1 ].
Check Accept 51 [1 pre10 atom0 ].
Check Reject 52 [0 pre10 atom0 ].

Check Reject 60 [1 pre00 atom1 ].
Check Reject 61 [0 pre00 atom1 ].
Check Accept 62 [0 pre00 atom0 ].

Check Reject 70 [0 pre0x atom0 ].

Check Reject 80 [2 atom3 post12 ].
Check Reject 81 [2 atom2 post12 ].
Check Accept 82 [2 atom1 post12 ].
Check Reject 83 [1 atom1 post12 ].

Check Reject 90 [2 atom2 post11 ].
Check Accept 91 [2 atom1 post11 ].
Check Accept 92 [1 atom1 post11 ].
Check Reject 93 [0 atom1 post11 ].

Check Reject 100 [3 atom3 op22 atom2 ].
Check Reject 101 [3 atom2 op22 atom3 ].
Check Accept 102 [3 atom2 op22 atom2 ].
Check Reject 103 [2 atom2 op22 atom2 ].

Check Reject 110 [2 atom2 op12 atom2 ].
Check Reject 111 [2 atom1 op12 atom3 ].
Check Accept 112 [2 atom1 op12 atom2 ].
Check Reject 113 [1 atom1 op12 atom2 ].

Check Reject 120 [1 atom2 op10 atom0].
Check Reject 121 [1 atom1 op10 atom1].
Check Accept 122 [1 atom1 op10 atom0].
Check Reject 123 [0 atom1 op10 atom0].

Check Reject 130 [2 pre22 atom2 op12 atom2 ].
Check Reject 131 [2 pre21 atom1 op12 atom2 ].
Check Accept 132 [2 pre22 atom1 op12 atom2 ].

Check Reject 140 [2 atom2 post12 op12 atom2 ].
Check Reject 141 [2 atom1 post12 op12 atom2 ].
Check Accept 142 [2 atom1 post11 op12 atom2 ].

Check Accept 150 [2 atom1 op12 pre22 atom2 ].
Check Reject 151 [2 atom1 op12 pre21 atom2 ].
Check Accept 152 [2 atom1 op12 pre21 atom1 ].

Check Reject 160 [2 atom1 op12 atom2 post12 ].
Check Accept 161 [2 atom1 op12 atom1 post12 ].
Check Reject 162 [2 atom1 op10 atom1 post12 ].
Check Accept 163 [2 atom1 op10 atom0 post12 ].

Check Accept 170 [1 pre11 atom1 op10 atom0 ].
Check Reject 171 [1 pre10 atom1 op10 atom0 ].
Check Accept 172 [1 pre10 atom0 op10 atom0 ].

Check Reject 180 [1 atom1 post12 op10 atom0 ].
Check Accept 181 [1 atom1 post11 op10 atom0 ].

Check Reject 190 [1 atom1 op10 pre11 atom0 ].
Check Reject 191 [1 atom1 op10 pre10 atom0 ].

Check Accept 200 [2 atom1 op10 atom0 post12 ].
Check Reject 201 [1 atom1 op10 atom0 post12 ].
Check Accept 202 [1 atom1 op10 atom0 post11 ].

Check Reject 210 [2 atom1 op12 atom2 op12 atom2 ].
Check Accept 211 [2 atom1 op12 atom1 op12 atom2 ].

Check Reject 220 [1 atom1 op10 atom1 op10 atom0 ].
Check Accept 221 [1 atom1 op10 atom0 op10 atom0 ].

From Corelib Require Import Notations.

Tactic Notation (at level 5) "atom5" := idtac.
Tactic Notation (at level 4) "atom4" := idtac.
Tactic Notation (at level 3) "atom3" := idtac.
Tactic Notation (at level 2) "atom2" := idtac.
Tactic Notation (at level 1) "atom1" := idtac.

Tactic Notation (at level 4) "pre44" tactic4(x) := x.
Tactic Notation (at level 4) "pre43" tactic3(x) := x.
Tactic Notation (at level 2) "pre22" tactic2(x) := x.
Tactic Notation (at level 2) "pre21" tactic1(x) := x.

Tactic Notation (at level 4) tactic4(x) "post44" := x.
Tactic Notation (at level 2) tactic2(x) "post12" := x.

Print Grammar tactic.

Check Reject 230 ltac:(atom5 ; atom3).
Check Reject 231 ltac:(atom4 ; atom4).
Check Accept 232 ltac:(atom4 ; atom3).
Check Accept 233 ltac:(atom4 ; atom3 ; atom3).

Check Reject 240 ltac:(pre43 atom4 ; atom3).
Check Accept 241 ltac:(pre43 atom3 ; atom3).
Check Reject 242 ltac:(pre44 atom4 ; atom3).
Check Accept 243 ltac:(pre44 atom3 ; atom3).

Check Accept 250 ltac:(atom4 post44 ; atom3).
Check Accept 251 ltac:(atom4 ; atom3 post44).

Check Reject 260 ltac:(atom2 + atom2).
Check Reject 261 ltac:(atom1 + atom3).
Check Accept 262 ltac:(atom1 + atom2).
Check Accept 263 ltac:(atom1 + atom1 + atom2).

Check Reject 270 ltac:(pre22 atom2 + atom2).
Check Reject 271 ltac:(pre21 atom1 + atom2).
Check Accept 272 ltac:(pre22 atom1 + atom2).
Check Accept 273 ltac:(atom1 + pre22 atom2).

Check Reject 280 ltac:(atom1 post12 + atom2).
Check Reject 281 ltac:(atom1 + atom2 post12).
Check Accept 282 ltac:(atom1 + atom1 post12).
