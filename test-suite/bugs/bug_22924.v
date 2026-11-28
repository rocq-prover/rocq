(* Regression test for wrong binder relevance on SProp inductives in env_ar:
   distinct mutual SProp inductives and differently indexed SProp inductives
   must not be equated during constructor typechecking. *)

Fail CoInductive sTrue : SProp :=
| sI : let cast : sTrue -> sFalse := fun x : sTrue => x in sTrue
with sFalse : SProp := .

(* Previously the above succeeded and allowed:
   Definition boom : sFalse := match sI with sI cast => cast sI end.
   Definition contradiction : False := match boom return False with end.
*)

Fail Inductive sTrue' : SProp :=
| sI' : let cast : sTrue' -> sFalse' := fun x : sTrue' => x in sTrue'
with sFalse' : SProp := .

Inductive two : Set := t0 | t1.

Fail CoInductive I : two -> SProp :=
| c : let cast : I t0 -> I t1 := fun x : I t0 => x in I t0.

(* Valid mutual SProp inductives still typecheck. *)
CoInductive validA : SProp :=
| cA : let id : validA -> validA := fun x : validA => x in validB -> validA
with validB : SProp :=
| cB : validB.

Inductive validIndA : SProp :=
| cIndA : validIndB -> validIndA
with validIndB : SProp :=
| cIndB : validIndB.
