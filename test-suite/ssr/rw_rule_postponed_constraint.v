From Corelib Require Import ssreflect ssrbool.

(* The unification problems postponed when interpreting a rewrite rule
   (here [?P 0 == true], from [isT]) must constrain its instances: the first
   subterm matching the LHS, [foo neq0 f], is not an instance. *)

Axiom foo : (nat -> bool) -> (nat -> nat) -> nat.
Axiom bar : (nat -> bool) -> (nat -> nat) -> nat.
Axiom fooE : forall (P : nat -> bool) f, P 0 -> foo P f = bar P f.

Definition neq0 (i : nat) := match i with 0 => false | _ => true end.

Lemma test f :
  foo neq0 f + foo (fun _ => true) f = foo neq0 f + bar (fun _ => true) f.
Proof.
rw (fooE _ _ isT).
reflexivity.
Qed.
