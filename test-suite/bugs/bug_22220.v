(* Schemes over template polymorphic inductives (Scheme Rewriting) should
   not mention the global template universes in their types, so that using
   them does not constrain the template universes.
   See https://github.com/rocq-prover/rocq/issues/22220 *)
Set Warnings "+bad-template-constraint".

(* Eta-expansion constrains the universe of the first argument; this must
   not touch eq.u0. *)
Check (fun x => @eq_sym x).
Check (fun x => @eq_sym_involutive x).
Check (fun x => @eq_rew x).
Check (fun x => @eq_rew_dep x).
Check (fun x => @eq_rew_fwd_dep x).
Check (fun x => @eq_rew_r x).
Check (fun x => @eq_rew_r_dep x).
Check (fun x => @eq_rew_fwd_r_dep x).

(* These were already fine and must stay so. *)
Check (fun x => @eq_ind x).
Check (fun x => @eq_rect x).
Check (fun x => @eq_trans x).
Check (fun x => @f_equal x).

(* The schemes must still be usable at arbitrary universes. *)
Goal forall (A : Type) (x y : A), x = y -> y = x.
Proof. intros A x y H. exact (eq_sym H). Qed.

(* Scheme generation itself must also work with the warning as error. *)
Inductive myeq (A:Type) (x:A) : A -> Prop := myeq_refl : myeq A x x.
Scheme Rewriting for myeq.
Check (fun x => @myeq_sym x).
Check (fun x => @myeq_sym_involutive x).
Check (fun x => @myeq_rew_r_dep x).
