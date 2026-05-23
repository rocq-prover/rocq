(* Test for bug #22058: contract_case anomaly on evar-backed and LetIn-inlined branches *)

From Ltac2 Require Import Ltac2 Constr.

(* Reproducer 1: evar-backed Lambda bodies *)

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

(* Reproducer 2: LetIn inlining *)

Unset Primitive Projections.
Record MyRec := mkMyRec {
  field1 : nat;
  field2 : nat := field1 + 1;
  field3 : nat
}.

Ltac2 trigger () :=
  let f := constr:(fun (r : MyRec) => match r with mkMyRec a b c => a + b + c end) in
  match Unsafe.kind f with
  | Unsafe.Lambda _ body =>
    match Unsafe.kind body with
    | Unsafe.Case ci (ret, rel) iv scrut branches =>
      let br := Array.get branches 0 in
      let rec inline (c : constr) : constr :=
        match Unsafe.kind c with
        | Unsafe.Lambda b body => Unsafe.make (Unsafe.Lambda b (inline body))
        | Unsafe.LetIn _b v body =>
          let inlined := Unsafe.substnl [v] 0 body in
          inline inlined
        | _ => c
        end in
      let br' := inline br in
      let branches' := Array.make 1 br' in
      let _ := Constr.Unsafe.make
        (Unsafe.Case ci (ret, rel) iv scrut branches') in
      ()
    | _ => ()
    end
  | _ => ()
  end.

Goal True. trigger (). Abort.
