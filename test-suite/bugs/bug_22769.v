(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)

Symbol f : nat -> nat -> nat.
Rewrite Rule r := f ?x => fun _ : nat => ?x.

Check eq_refl : (fun z : nat => f z) = (fun z _ => z).
(* Used to be (fun _ z => z) *)
