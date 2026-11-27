(* -*- coqchk-prog-args: ("-bytecode-compiler" "yes") -*- *)

(* When the VM eta-expands a mutual fixpoint, it must keep the component it
   expands: each component is its own eta-expansion, and no other one. *)

Fixpoint p (n : nat) : nat := match n with 0 => 0 | S m => q m end
with     q (n : nat) : nat := match n with 0 => 1 | S m => p m end.

Definition p_eta := eq_refl (fun n => p n) <: (fun n => p n) = p.
Definition q_eta := eq_refl (fun n => q n) <: (fun n => q n) = q.
Fail Check eq_refl (fun n => q n) <: (fun n => q n) = p.

Fixpoint ev (c n : nat) : nat := match n with 0 => c | S m => od c m end
with     od (c n : nat) : nat := match n with 0 => S c | S m => ev c m end.

Definition ev_eta := eq_refl (fun c => ev c) <: (fun c => ev c) = ev.
Definition ev_c_eta (c : nat) := eq_refl (fun n => ev c n) <: (fun n => ev c n) = ev c.
Fail Check eq_refl (fun c => od c) <: (fun c => od c) = ev.
Fail Check fun c : nat => eq_refl (fun n => od c n) <: (fun n => od c n) = ev c.

Fixpoint fa (n : nat) : nat -> nat := match n with 0 => fun x => x | S m => fb m end
with     fb (n : nat) : nat -> nat := match n with 0 => S | S m => fa m end.

Definition fa_eta (n : nat) := eq_refl (fun x => fa n x) <: (fun x => fa n x) = fa n.
Fail Check fun n : nat => eq_refl (fun x => fb n x) <: (fun x => fb n x) = fa n.

Fixpoint ga (n x : nat) : nat -> nat := match n with 0 => plus x | S m => gb m x end
with     gb (n x : nat) : nat -> nat := match n with 0 => mult x | S m => ga m x end.

Definition ga_eta (n x : nat) := eq_refl (fun y => ga n x y) <: (fun y => ga n x y) = ga n x.
Fail Check fun n x : nat => eq_refl (fun y => gb n x y) <: (fun y => gb n x y) = ga n x.
