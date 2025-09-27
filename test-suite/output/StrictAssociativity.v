Inductive T := E : T | F : T -> T | G : T -> T -> T.
Inductive Check_If_Warning_Above {A} := Pass (_ : nat) (_ : A) | Warn (_ : nat) (_ : A).

Declare Custom Entry expr.

Notation "x 'op22' y" := (G x y) (in custom expr at level 3, no associativity).
Notation "x 'op12' y" := (G x y) (in custom expr at level 2, right associativity).
Notation "x 'op10' y" := (G x y) (in custom expr at level 1, left associativity).

Notation "[3 e ]" := e (e custom expr at level 3, only parsing).
Notation "[2 e ]" := e (e custom expr at level 2, only parsing).
Notation "[1 e ]" := e (e custom expr at level 1, only parsing).
Notation "[0 e ]" := e (e custom expr at level 0, only parsing).

Notation "'atom3'" := E (in custom expr at level 3, only parsing).
Notation "'atom2'" := E (in custom expr at level 2, only parsing).
Notation "'atom1'" := E (in custom expr at level 1, only parsing).
Notation "'atom0'" := E (in custom expr at level 0, only parsing).

Notation "'pre22' x" := (F x) (in custom expr at level 2, x at level 2, only parsing).
Notation "'pre21' x" := (F x) (in custom expr at level 2, only parsing).
Notation "'pre11' x" := (F x) (in custom expr at level 1, x at level 1, only parsing).
Notation "'pre10' x" := (F x) (in custom expr at level 1, only parsing).

Notation "x 'post12'" := (F x) (in custom expr at level 2, only parsing).
Notation "x 'post11'" := (F x) (in custom expr at level 1, only parsing).

Print Custom Grammar expr.

(* The following sed script prints the first line with a wrong result:

     sed -n '/^Warn /{x;/level-tolerance/!bf};/^Pass /{x;/level-tolerance/bf};h;b;:f;x;l;q1' \
       output/StrictAssociativity.out

   The script checks that:
   - Each line starting with "Warn " is preceded by a line containing "level-tolerance"
   - Each line starting with "Pass " is preceded by a line not containing "level-tolerance"

   In case of failure, it prints the line containing "Warn " or "Pass ". *)

Check Warn 10 [2 atom3 ].
Check Pass 11 [2 atom2 ].
Check Warn 12 [1 atom2 ].
Check Pass 13 [1 atom1 ].

Check Warn 20 [2 pre22 atom3 ].
Check Pass 21 [2 pre22 atom2 ].
Check Warn 22 [1 pre22 atom2 ].

Check Warn 30 [2 pre21 atom2 ].
Check Pass 31 [2 pre21 atom1 ].
Check Warn 32 [1 pre21 atom1 ].

Check Warn 40 [2 pre11 atom2 ].
Check Warn 41 [1 pre11 atom2 ].
Check Pass 42 [1 pre11 atom1 ].
Check Warn 43 [0 pre11 atom1 ].

Check Warn 50 [1 pre10 atom1 ].
Check Pass 51 [1 pre10 atom0 ].
Check Warn 52 [0 pre10 atom0 ].

Check Warn 60 [2 atom2 post12 ].
Check Pass 61 [2 atom1 post12 ].
Check Warn 62 [1 atom1 post12 ].

Check Warn 70 [2 atom2 post11 ].
Check Pass 71 [2 atom1 post11 ].
Check Pass 72 [1 atom1 post11 ].
Check Warn 73 [0 atom1 post11 ].

Check Warn 80 [3 atom3 op22 atom2 ].
Check Warn 81 [3 atom2 op22 atom3 ].
Check Pass 82 [3 atom2 op22 atom2 ].
Check Warn 83 [2 atom2 op22 atom2 ].

Check Warn 90 [2 atom2 op12 atom2 ].
Check Warn 91 [2 atom1 op12 atom3 ].
Check Pass 92 [2 atom1 op12 atom2 ].
Check Warn 93 [1 atom1 op12 atom2 ].

Check Warn 100 [1 atom2 op10 atom0].
Check Warn 101 [1 atom1 op10 atom1].
Check Pass 102 [1 atom1 op10 atom0].
Check Warn 103 [0 atom1 op10 atom0].

Check Warn 110 [2 pre22 atom2 op12 atom2 ].
Check Warn 111 [2 pre21 atom1 op12 atom2 ].
Check Pass 112 [2 pre22 atom1 op12 atom2 ].

Check Warn 120 [2 atom2 post12 op12 atom2 ].
Check Warn 121 [2 atom1 post12 op12 atom2 ].
Check Pass 122 [2 atom1 post11 op12 atom2 ].

Check Pass 130 [2 atom1 op12 pre22 atom2 ].
Check Warn 131 [2 atom1 op12 pre21 atom2 ].
Check Pass 132 [2 atom1 op12 pre21 atom1 ].

Check Warn 140 [2 atom1 op12 atom2 post12 ].
Check Pass 141 [2 atom1 op12 atom1 post12 ].
Check Warn 142 [2 atom1 op10 atom1 post12 ].
Check Pass 143 [2 atom1 op10 atom0 post12 ].

Check Pass 150 [1 pre11 atom1 op10 atom0 ].
Check Warn 151 [1 pre10 atom1 op10 atom0 ].
Check Pass 152 [1 pre10 atom0 op10 atom0 ].

Check Warn 160 [1 atom1 post12 op10 atom0 ].
Check Pass 161 [1 atom1 post11 op10 atom0 ].

Check Warn 170 [1 atom1 op10 pre11 atom0 ].
Check Warn 171 [1 atom1 op10 pre10 atom0 ].

Check Pass 180 [2 atom1 op10 atom0 post12 ].
Check Warn 181 [1 atom1 op10 atom0 post12 ].
Check Pass 182 [1 atom1 op10 atom0 post11 ].

Check Warn 190 [2 atom1 op12 atom2 op12 atom2 ].
Check Pass 191 [2 atom1 op12 atom1 op12 atom2 ].

Check Warn 200 [1 atom1 op10 atom1 op10 atom0 ].
Check Pass 201 [1 atom1 op10 atom0 op10 atom0 ].

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
Tactic Notation (at level 2) tactic2(x) "post22" := x.

Print Grammar tactic.

Check Warn 1000 ltac:(atom5 ; atom3).
(* Check Warn 1001 ltac:(atom4 ; atom4). (* generates an error *) *)
Check Pass 1002 ltac:(atom4 ; atom3).
Check Pass 1003 ltac:(atom4 ; atom3 ; atom3).

(* Check Warn 1010 ltac:(pre43 atom4 ; atom3). (* generates an error *) *)
Check Pass 1011 ltac:(pre43 atom3 ; atom3).
(* Check Pass 1012 ltac:(pre44 atom4 ; atom3). (* generates an error *) *)
Check Pass 1013 ltac:(pre44 atom3 ; atom3).

Check Pass 1020 ltac:(atom4 post44 ; atom3).
Check Pass 1021 ltac:(atom4 ; atom3 post44).

Check Warn 1100 ltac:(atom2 + atom2).
Check Warn 1101 ltac:(atom1 + atom3).
Check Pass 1102 ltac:(atom1 + atom2).
Check Pass 1103 ltac:(atom1 + atom1 + atom2).

Check Warn 1110 ltac:(pre22 atom2 + atom2).
Check Warn 1111 ltac:(pre21 atom1 + atom2).
Check Pass 1112 ltac:(pre22 atom1 + atom2).
Check Pass 1113 ltac:(atom1 + pre22 atom2).

Check Warn 1120 ltac:(atom1 post22 + atom2).
Check Warn 1121 ltac:(atom1 + atom2 post22).
Check Pass 1122 ltac:(atom1 + atom1 post22).
