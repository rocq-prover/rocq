
Module M.
  Private Inductive foo := .

  Definition to_nat (f:foo) : nat := match f with end.
End M.

Lemma bar : False.
Proof.
  exact_no_check I.
  Fail Validate Proof.
Abort.

Lemma bar f : M.to_nat f = 0.
Proof.
  Validate Proof.

  cbv.

  Fail Validate Proof.

Abort.

Goal Type.
Proof.
  exact_no_check Type.
  Fail Validate Proof.
Abort.

Polymorphic Record Box@{s;} (A:Prop) : Type@{s;Set} := box { unbox : A }.
Arguments box {_}. Arguments unbox {_}.

From Ltac2 Require Import Ltac2 Constr.
Import Constr.Unsafe.

Polymorphic Lemma foo@{s;} (A:Prop) (x:Box@{s;} A) : A.
Proof.
  let ind := match reference:(Box) with Std.IndRef ind => ind | _ => Control.throw Assertion_failure end in
  let case := Constr.Unsafe.case ind in
  let c := make (Case case ('(fun _:Box@{s;} A => A), Relevance.relevant) NoInvert '&x [|'(fun (b:A) => b)|]) in
  exact $c.
  Fail Validate Proof.
Abort.
