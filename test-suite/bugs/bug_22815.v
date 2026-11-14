(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)

Inductive box := G : list nat -> box.

Symbol F : (nat -> box) -> nat -> nat -> box.

Rewrite Rule r := F (fun x => G ?a) => fun (_ : nat) (y : nat) => G ?a@{x := y}.

Check eq_refl : (fun z : nat => F (fun x => G (cons x (cons z nil)))) = (fun z _ y => G (y :: z :: nil)).
(* Originally found [fun z H _ => G (H :: z :: nil)] *)
