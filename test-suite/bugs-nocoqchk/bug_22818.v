(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)

Inductive box := G : list nat -> box.

Axiom P : list nat -> Set.

Axiom Q : (nat -> Set) -> Set.

Symbol T : (nat -> box) -> Set.

Rewrite Rule r := T (fun x => G ?a) => forall (w : nat) (y : nat), Q (fun v : nat => P ?a@{x := y}).

Definition e (z : nat) (f : T (fun x => G (cons x (cons z nil)))) := f 1 0.

Check e : forall z (f : T (fun x => G (cons x (cons z nil)))), Q (fun _ => P (0 :: z :: nil)).
(* Used to be [forall z f, Q (fun _ => P (0 :: f :: nil))] *)
