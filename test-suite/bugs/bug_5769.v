(* Check a few naming heuristics based on types *)
(* was buggy for types names _something *)

Inductive _foo :=.
Lemma bob : (sigT (fun x : nat => _foo)) -> _foo.
destruct 1.
exact _f.
Abort.

Inductive _'Foo :=.
Lemma bob : (sigT (fun x : nat => _'Foo)) -> _'Foo.
destruct 1.
exact _'f.
Abort.

Inductive ____foo :=.
Lemma bob : (sigT (fun x : nat => ____foo)) -> ____foo.
destruct 1.
exact ____f.
Abort.
