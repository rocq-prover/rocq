(* -*- coq-prog-args: ("-async-proofs" "on"); -*- *)

(* The proof below is delegated to a worker, where [abstract] declares
   a private constant whose universe becomes a global level, created by
   the worker. It must not clash with the global levels created by the
   main process, here [a] and [b] (otherwise [b < u], for the universe [u] of
   the statement, could read [b < a]). *)

Universes a b.
Constraint a < b.

Lemma worker_univ : Type.
Proof.
  abstract exact Type@{b}.
Qed.
