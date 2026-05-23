Require Import Ltac2.Ltac2.
Import Constr.Unsafe.

(** Test Unsafe.in_context with None (LocalAssum) *)
Goal True.
  let r := Constr.Unsafe.in_context @x 'nat None (fun () =>
    Control.refine (fun () => 'True)) in
  let (b, body) := r in
  (* Reconstruct Lambda to check the result *)
  let c := make (Lambda b body) in
  let expected := '(fun x : nat => True) in
  if Constr.equal c expected then ()
  else Control.throw (Invalid_argument (Some (Message.concat
    (Message.of_string "Unsafe.in_context None: expected ")
    (Message.concat (Message.of_constr expected)
    (Message.concat (Message.of_string " but got ")
    (Message.of_constr c))))));
  exact I.
Qed.

(** Test Unsafe.in_context with Some (LocalDef) *)
Goal True.
  let r := Constr.Unsafe.in_context @x 'nat (Some '0) (fun () =>
    Control.refine (fun () => 'True)) in
  let (b, body) := r in
  (* Reconstruct LetIn to check the result *)
  let c := make (LetIn b '0 body) in
  let expected := '(let x : nat := 0 in True) in
  if Constr.equal c expected then ()
  else Control.throw (Invalid_argument (Some (Message.concat
    (Message.of_string "Unsafe.in_context Some: expected ")
    (Message.concat (Message.of_constr expected)
    (Message.concat (Message.of_string " but got ")
    (Message.of_constr c))))));
  exact I.
Qed.

(** Test in_context_prod *)
Goal True.
  let c := Constr.in_context_prod @x 'nat (fun () =>
    Control.refine (fun () => 'True)) in
  match kind c with
  | Prod _ _ => ()
  | _ => Control.throw (Invalid_argument (Some (Message.of_string "expected Prod")))
  end;
  (* Check that the result is [forall x : nat, True] *)
  let expected := '(forall x : nat, True) in
  if Constr.equal c expected then ()
  else Control.throw (Invalid_argument (Some (Message.concat
    (Message.of_string "in_context_prod: expected ")
    (Message.concat (Message.of_constr expected)
    (Message.concat (Message.of_string " but got ")
    (Message.of_constr c))))));
  exact I.
Qed.

(** Test in_context_letin *)
Goal True.
  let c := Constr.in_context_letin @x 'nat '0 (fun () =>
    Control.refine (fun () => 'True)) in
  match kind c with
  | LetIn _ _ _ => ()
  | _ => Control.throw (Invalid_argument (Some (Message.of_string "expected LetIn")))
  end;
  (* Check that the result is [let x : nat := 0 in True] *)
  let expected := '(let x : nat := 0 in True) in
  if Constr.equal c expected then ()
  else Control.throw (Invalid_argument (Some (Message.concat
    (Message.of_string "in_context_letin: expected ")
    (Message.concat (Message.of_constr expected)
    (Message.concat (Message.of_string " but got ")
    (Message.of_constr c))))));
  exact I.
Qed.

(** Test that in_context_letin makes the body available in the context *)
Goal True.
  let c := Constr.in_context_letin @x 'nat '0 (fun () =>
    (* x should be definitionally equal to 0 *)
    Control.refine (fun () => '(eq_refl : x = 0))) in
  match kind c with
  | LetIn _ _ _ => ()
  | _ => Control.throw (Invalid_argument (Some (Message.of_string "expected LetIn")))
  end;
  exact I.
Qed.
