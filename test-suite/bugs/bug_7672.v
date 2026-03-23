From Corelib Require Import BinNums IntDef NatDef.
Open Scope Z_scope.

Module First.
Lemma foo: forall (a b: nat),
    b < a ->
    a - b + b = a.
Admitted.

Axiom leb_spec : forall x y, (Nat.leb (S x) y) = true -> x < y.
Ltac solve_leb :=
  match goal with
  | [ |- ?x < ?y ] => apply leb_spec; exact eq_refl
  end.
Hint Rewrite foo using solve_leb : foo_db.

Goal (4 - 5 + 5) + (3 - 2 + 2) + (1 - 3 + 3) + 1 = (6 - 4 + 4) + (5 - 6 + 6).
Proof.
  (* I want to simplify (3 - 2 + 2) and (6 - 4 + 4), and leave the rest unchanged. *)

  (* This does not work because rewrite does not backtrack: *)
  repeat rewrite foo by solve_leb.
  match goal with
  | [ |-  4 - 5 + 5 + 3 + (1 - 3 + 3) + 1 = 6 + (5 - 6 + 6) ] => fail
  | _ => idtac
  end.

  (* This works! (but "rewrite*" is not documented) *)
  repeat rewrite* foo by solve_leb.
  match goal with
  | [ |-  4 - 5 + 5 + 3 + (1 - 3 + 3) + 1 = 6 + (5 - 6 + 6) ] => idtac
  end.

  Restart.

  (* autorewrite does not work: *)
  autorewrite with foo_db.
  match goal with
  | [ |-  4 - 5 + 5 + 3 + (1 - 3 + 3) + 1 = 6 + (5 - 6 + 6) ] => fail
  | _ => idtac
  end.
  Restart.

  (* Analogously, autorewrite* should work, but it does not!
     FEATURE REQUEST: Make this work *)
  autorewrite* with foo_db.
  match goal with
  | [ |-  4 - 5 + 5 + 3 + (1 - 3 + 3) + 1 = 6 + (5 - 6 + 6) ] => idtac
  end.
  Restart.

  (* For the record, a verbose workaround: *)
  repeat match goal with
  | |- context [?a - ?b + ?b] => rewrite (foo a b) by solve_leb
         end.
  match goal with
  | [ |-  4 - 5 + 5 + 3 + (1 - 3 + 3) + 1 = 6 + (5 - 6 + 6) ] => idtac
  end.
  reflexivity.
Qed.
End First.
Module Second.
Axiom cond : Z -> Prop.
Axiom rewrite : forall z, cond z -> z = Z0.

Global Hint Rewrite
  rewrite
  using assumption
: max.

Axiom have_cond: forall j, cond j.

Goal forall i j, cond i -> Z.max i j = Z.max i Z0.
Proof.
  intros.
  autorewrite with max.  (* works as expected    *)
  autorewrite* with max.  (* works as expected    *)
  pose proof (have_cond j).
  autorewrite* with max.
  reflexivity.
Qed.
End Second.
