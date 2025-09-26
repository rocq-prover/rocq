Set Warnings "+level-tolerance".

Inductive T := E : T | F : T -> T | G : T -> T -> T.

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

(* Check [2 atom3 ]. *)
Check [2 atom2 ].
(* Check [1 atom2 ]. *)
Check [1 atom1 ].

(* Check [2 pre22 atom3 ]. *)
Check [2 pre22 atom2 ].
(* Check [1 pre22 atom2 ]. *)

(* Check [2 pre21 atom2 ]. *)
Check [2 pre21 atom1 ].
(* Check [1 pre21 atom1 ]. *)

(* Check [2 pre11 atom2 ]. *)
(* Check [1 pre11 atom2 ]. *)
Check [1 pre11 atom1 ].
(* Check [0 pre11 atom1 ]. *)

(* Check [1 pre10 atom1 ]. *)
Check [1 pre10 atom0 ].
(* Check [0 pre10 atom0 ]. *)

(* Check [2 atom2 post12 ]. (* FIXED *) *)
Check [2 atom1 post12 ].
(* Check [1 atom1 post12 ]. *)

(* Check [2 atom2 post11 ]. *)
Check [2 atom1 post11 ].
Check [1 atom1 post11 ].
(* Check [0 atom1 post11 ]. *)

(* Check [3 atom3 op22 atom2 ]. (* FIXED *) *)
(* Check [3 atom2 op22 atom3 ]. *)
Check [3 atom2 op22 atom2 ].
(* Check [2 atom2 op22 atom2 ]. *)

(* Check [2 atom2 op12 atom2 ]. (* FIXED *) *)
(* Check [2 atom1 op12 atom3 ]. *)
Check [2 atom1 op12 atom2 ].
(* Check [1 atom1 op12 atom2 ]. *)

(* Check [1 atom2 op10 atom0]. *)
(* Check [1 atom1 op10 atom1]. *)
Check [1 atom1 op10 atom0].
(* Check [0 atom1 op10 atom0]. *)

(* Check [2 pre22 atom2 op12 atom2 ]. (* FIXED *) *)
(* Check [2 pre21 atom1 op12 atom2 ]. (* FIXED *) *)
Check [2 pre22 atom1 op12 atom2 ].

(* Check [2 atom2 post12 op12 atom2 ]. (* FIXED *) *)
(* Check [2 atom1 post12 op12 atom2 ]. (* FIXED *) *)
Check [2 atom1 post11 op12 atom2 ].

Check [2 atom1 op12 pre22 atom2 ].
(* Check [2 atom1 op12 pre21 atom2 ]. *)
Check [2 atom1 op12 pre21 atom1 ].

(* Check [2 atom1 op12 atom2 post12 ]. (* FIXED *) *)
Check [2 atom1 op12 atom1 post12 ].
(* Check [2 atom1 op10 atom1 post12 ]. *)
Check [2 atom1 op10 atom0 post12 ].

Check [1 pre11 atom1 op10 atom0 ].
(* Check [1 pre10 atom1 op10 atom0 ]. *)
Check [1 pre10 atom0 op10 atom0 ].

(* Check [1 atom1 post12 op10 atom0 ]. *)
Check [1 atom1 post11 op10 atom0 ].

(* Check [1 atom1 op10 pre11 atom0 ]. *)
(* Check [1 atom1 op10 pre10 atom0 ]. *)

Check [2 atom1 op10 atom0 post12 ].
(* Check [1 atom1 op10 atom0 post12 ]. *)
Check [1 atom1 op10 atom0 post11 ].

(* Examples of warn_recover error messages with wrong levels and span. *)
(* Check [2 atom3 post11 ]. *)
(* Check [2 atom3 post12 ]. *)
