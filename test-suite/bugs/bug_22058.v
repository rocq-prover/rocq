(* Test for bug #22058: contract_case anomaly on evar-backed branches *)

From Ltac2 Require Import Ltac2 Constr.

(* Reproducer: evar-backed Lambda bodies *)
(* When Constr.in_context creates Lambda terms whose bodies are solved evars,
   unsafe_to_constr (identity) doesn't resolve them, so the kernel's
   decompose_lambda_n_decls_opt sees Evar instead of Lambda and fails. *)

Ltac2 make_evar_backed_branch () : constr :=
  Constr.in_context @a constr:(nat) (fun () =>
    let inner :=
      Constr.in_context @b constr:(nat) (fun () =>
        let a := Control.hyp @a in
        let b := Control.hyp @b in
        Control.refine (fun () => constr:(Nat.add $a $b))) in
    Control.refine (fun () => inner)).

Goal True.
  let template := constr:(fun (p : nat * nat) => let '(a, b) := p in a + b) in
  match Unsafe.kind template with
  | Unsafe.Lambda _ body =>
    match Unsafe.kind body with
    | Unsafe.Case ci retrel iv scrut _branches =>
      let new_branch := make_evar_backed_branch () in
      let branches := Array.make 1 new_branch in
      let _ := Constr.Unsafe.make (Unsafe.Case ci retrel iv scrut branches) in
      ()
    | _ => ()
    end
  | _ => ()
  end.
Abort.
