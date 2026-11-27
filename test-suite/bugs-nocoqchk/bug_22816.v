(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)

Inductive box := G : nat -> box | H : (nat -> box) -> box.

Symbol F : (nat -> box) -> nat -> box.

Rewrite Rule r := F (fun x => H (fun w => G ?a)) => fun y => G ?a@{x := y; w := y}.

Check eq_refl : F (fun x => (fun v => H (fun w => G v)) (S x)) = fun y => G (S y).
(* Anomaly "File "kernel/cClosure.ml", line 304, characters 13-19: Assertion failed." *)
