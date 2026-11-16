(* Test regression https://github.com/rocq-prover/rocq/issues/16140
   where congruence produces ill-typed terms *)

Inductive wrap1 : Type :=
  wrap1I (u : unit) : match u with tt => bool end -> wrap1.

Goal (wrap1I tt false) = (wrap1I tt true) -> False.
Proof.
  Fail congruence. (* expected to fail *)
Abort.

Inductive wrap2 : unit -> Type :=
  wrap2I (u : unit) : match u with tt => bool end -> wrap2 u.

Goal (wrap2I tt false) = (wrap2I tt true) -> False.
Proof.
  Fail congruence. (* expected to fail *)
Abort.

Inductive wrap3 (u : unit) : Type :=
  wrap3I : match u with tt => bool end -> wrap3 u.

Goal (wrap3I tt false) = (wrap3I tt true) -> False.
Proof.
  congruence.
Qed.

Inductive wrap4 : Type :=
  wrap4I (n : nat) : (fun _ => bool) n -> wrap4.

Goal (wrap4I 0 false) = (wrap4I 0 true) -> False.
Proof.
  congruence.
Qed.
