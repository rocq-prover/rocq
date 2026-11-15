(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)

Ltac kernel_refl := match goal with |- @eq ?T ?a _ => exact_no_check (@eq_refl T a) end.

Module ClosureEnv.

Inductive box := G : list nat -> box.

Symbol F : (nat -> box) -> nat -> nat -> box.

Rewrite Rule r := F (fun x => G ?a) => fun (_ : nat) (y : nat) => G ?a@{x := y}.

Lemma l1 : (fun z : nat => F (fun x => G (cons x (cons z nil)))) 1 = (fun _ y => G (y :: 1 :: nil)).
Proof. kernel_refl. Qed.

Lemma l2 : (fun z : nat => (fun t : nat => F (fun x => G (cons x (cons t (cons z nil))))) (S z))
  = (fun z _ y => G (y :: S z :: z :: nil)).
Proof. kernel_refl. Qed.

End ClosureEnv.

Module Lifted.

Inductive box := G : nat -> box | H : (nat -> box) -> box.

Symbol F : (nat -> box) -> nat -> nat -> box.

Rewrite Rule r := F (fun x => H (fun w => G ?a)) => fun y y2 => G ?a@{x := y; w := y2}.

Lemma l : F (fun x => (fun v => H (fun w => G (v + w))) (S x)) = fun y y2 => G (S y + y2).
Proof. kernel_refl. Qed.

End Lifted.

Module Construct.

Inductive box := P : list nat -> list nat -> box | H : (nat -> box) -> box.

Symbol F : (nat -> box) -> nat -> nat -> box.

Rewrite Rule r := F (fun x => H (fun w => P (cons ?h ?t) ?a)) => fun y y2 => P ?a@{x := y2; w := y} nil.

Lemma l1 : F (fun x => H (fun w => (fun v => P v v) (cons x nil))) = fun _ y2 => P (y2 :: nil) nil.
Proof. kernel_refl. Qed.

Lemma l2 : F (fun x => (fun v => H (fun w => P v v)) (cons x nil)) = fun _ y2 => P (y2 :: nil) nil.
Proof. kernel_refl. Qed.

End Construct.
