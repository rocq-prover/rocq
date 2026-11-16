(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)

Ltac kernel_refl := match goal with |- @eq ?T ?a _ => exact_no_check (@eq_refl T a) end.

Module Ind.

Symbol F : Set -> Set.

Rewrite Rule r := F (list ?A) => ?A.

Lemma l : (fun (A : Set) => (fun T : Set => fun w : Set => F T) (list A)) = (fun A w => A).
Proof. kernel_refl. Qed.

End Ind.

Module Sym.

Symbol K : nat -> nat.

Symbol F : nat -> nat.

Rewrite Rule r := F (K ?n) => ?n.

Lemma l : (fun (z : nat) => (fun t : nat => fun w : nat => F t) (K z)) = (fun z w => z).
Proof. kernel_refl. Qed.

End Sym.

Module Prod.

Symbol F : Set -> Set.

Rewrite Rule r := F (forall _ : ?A, ?B) => ?A.

Lemma l : (fun (A : Set) => (fun T : Set => fun w : Set => F T) (A -> nat)) = (fun A w => A).
Proof. kernel_refl. Qed.

End Prod.

Module Case.

Symbol K : nat.

Symbol F : nat -> nat.

Rewrite Rule r := F (match K with 0 => ?a | S _ => _ end) => ?a.

Lemma l : (fun (z : nat) => (fun t : nat => fun w : nat => F t) (match K with 0 => z | S _ => 0 end)) = (fun z w => z).
Proof. kernel_refl. Qed.

End Case.
