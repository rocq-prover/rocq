Require Import Setoid.

From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Std.
From Ltac2 Require Import Rewrite.

Import Strategy.

Parameter X : Set.

Parameter f : X -> X.
Parameter g : X -> X -> X.
Parameter h : nat -> X -> X.

Parameter lem0 : forall x, f (f x) = f x.
Parameter lem1 : forall x, g x x = f x.
Parameter lem2 : forall n x, h (S n) x = g (h n x) (h n x).
Parameter lem3 : forall x, h 0 x = x.

#[export] Hint Rewrite lem0 lem1 lem2 lem3 : rew.

Goal forall x, h 6 x = f x.
  intros.
  time (rewrite_strat (topdown (term preterm:(lem2) true)) None).
  time (rewrite_strat (topdown (term preterm:(lem1) true)) None).
  time (rewrite_strat (topdown (term preterm:(lem0) true)) None).
  time (rewrite_strat (topdown (term preterm:(lem3) true)) None).
  time (rewrite_strat id None).
  reflexivity ().
Undo 6.
  time (rewrite_strat (topdown
          (choice
             (term preterm:(lem2) true)
             (term preterm:(lem1) true)
       )) None).
  time (rewrite_strat (topdown
          (choice
             (term preterm:(lem0) true)
             (term preterm:(lem3) true)
       )) None).
  reflexivity ().
Undo 3.
  time (rewrite_strat (seq
                       (topdown
                          (choice
                             (term preterm:(lem2) true)
                             (term preterm:(lem1) true)
                       ))
                       (topdown
                          (choice
                             (term preterm:(lem0) true)
                             (term preterm:(lem3) true)
                          ))
       ) None).
  reflexivity ().
Undo 2.
  time (rewrite_strat (topdown
                         (choice
                              (choice
                                 (term preterm:(lem2) true)
                                 (term preterm:(lem1) true)
                              )
                              (choice
                                 (term preterm:(lem0) true)
                                 (term preterm:(lem3) true)
                              )
                         )
          ) None).
  reflexivity ().
Undo 2.
  time (rewrite_strat (topdown
                         (choice
                              (term preterm:(lem2) true)
                              (choice
                                 (term preterm:(lem1) true)
                                 (choice
                                    (term preterm:(lem0) true)
                                    (term preterm:(lem3) true)
                                 )
                            )
                         )
       ) None).
  reflexivity ().
Undo 2.
  time (rewrite_strat (topdown
                         (choices [
                              (term preterm:(lem2) true);
                              (term preterm:(lem1) true);
                              (term preterm:(lem0) true);
                              (term preterm:(lem3) true)
                            ]
                         )
          ) None).
  reflexivity ().
Undo 2.
  time (rewrite_strat (fix_
                         (fun f =>
                            seq
                              (choices [
                                   (term preterm:(lem2) true);
                                   (term preterm:(lem1) true);
                                   (term preterm:(lem0) true);
                                   (term preterm:(lem3) true);
                                   (progress (subterms f))
                                 ])
                            (try f)
                         )
       ) None).
  reflexivity ().
Qed.

Parameter breaker : forall x y, h x y = f y <-> False.

Goal forall x, h 10 x = f x.
Proof.
  intros.
  time (rewrite_strat (topdown (hints @rew)) None).
  reflexivity ().
Undo 2.
  time (rewrite_strat (any (outermost (hints @rew))) None).
  reflexivity ().
Undo 2.
  time (rewrite_strat (repeat (outermost (hints @rew))) None).
  reflexivity ().
Undo 2.
  time (rewrite_strat (seqs [outermost (Strategy.fold '(6 + ?[?four]))]) None).
  match! goal with
  | [|- h (6 + 4) ?x = f ?x] => ()
  | [|- _] => Control.throw Assertion_failure
  end.
Undo 2.
  time (rewrite_strat (
            choices [
                seqs [fail; term preterm:(breaker) true]; (* fail *)
                seqs [repeat fail; term preterm:(breaker) true];  (* fail *)
                seqs [progress fail; term preterm:(breaker) true];  (* fail *)
                seqs [progress id; term preterm:(breaker) true];  (* fail *)

                seqs [id;
                      progress refl;
                      any fail;
                      try fail;
                      topdown (hints @rew)
                  ];  (* success *)

                term preterm:(breaker) true  (* unreachable *)
       ]) None).
  reflexivity ().
Qed.

Set Printing All.
Set Printing Depth 100000.

Ltac2 Notation "my_rewrite_strat" x(preterm) := rewrite_strat (topdown (term x true)) None.
Goal (forall x, S x = 0) -> 1 = 0.
intro H.
my_rewrite_strat H.
Abort.

From Ltac2 Require Import Ltac2 Rewrite.
From Ltac2 Require Import Message.
Ltac2 msg x := print (of_string x).

Module StratLtac2Matches.

  Import Strategy.

  (* Heavy computation if unfolded at any point during unification *)
  Definition foo (n : nat) :=
    Nat.pow 2 n.

  Ltac2 rew_match carrier lhs _rel :=
   let rhs := Std.eval (Std.Red.vm None) lhs in
   Success {rel := '(@eq $carrier); rhs; prf := '(@eq_refl $carrier $rhs) }.

  Goal foo (200 + 200) = foo 400.
  Proof.
    rewrite_strat (bottomup (seq (matches pat:(Nat.add _ _)) (tactic rew_match))) None.
    match! goal with
    | [ |- foo 400 = foo 400 ] => id
    end.
    reflexivity.
  Qed.
End StratLtac2Matches.

Module StratLtac2Tactic.
  Import Strategy.

  Ltac2 is_closed_add t :=
    match! t with
    | Nat.add _ _ => true
    | _ => false
    end.

  Ltac2 reduce_fo_ind_value carrier lhs _rel :=
    if Constr.equal carrier '(nat) then
      if is_closed_add lhs then
        let ty := Constr.type lhs in
        let rhs := Std.eval (Std.Red.cbv RedFlags.all) lhs in
        Rewrite.Strategy.Success { rel := '(@eq $ty); rhs := rhs; prf := '(@eq_refl $ty $rhs) }
      else Fail
    else Fail.

  (* Heavy computation if unfolded at any point during unification *)
  Definition foo (n : nat) :=
    Nat.pow 2 n.

  Ltac2 reduce_fo_ind cl :=
    rewrite_strat (fix_ (fun s => choice (tactic reduce_fo_ind_value) (subterm s))) cl.

  Lemma heavy : foo (2000 + 2000) = foo 4000.
  Proof.
    reduce_fo_ind None.
    reflexivity.
  Qed.

  Axiom add_comm : forall (x y : nat), x + y = y + x.

  (* We use a flag to rewrite with a lemma only once *)
  Ltac2 Type flag := { mutable used : bool }.
  Import List.
  Ltac2 message_of_list f l :=
    List.fold_right (fun x acc => Message.concat (f x) acc) l Message.empty.

  Ltac2 of_hyps h :=
    message_of_list
      (fun (na, _, ty) =>
         Message.concat Message.space
           (Message.concat (of_ident na) (Message.concat (of_string " : ") (of_constr ty)))) h.

  Import Printf.

  Ltac2 rw_lemma fl lhs :=
    if fl.(used) then Fail else
      (let h := Control.hyps () in
       let concl := Control.goal () in
       printf "lhs = %t, goal = %m |- %t" lhs (of_hyps h) concl;
    match! lhs with
    | Nat.add ?l ?r =>
        fl.(used) := true;
        Strategy.Success { rel := '(@eq nat); rhs := '(Nat.add $r $l); prf := '(add_comm $l $r) }
    | _ => Fail
    end).

  Ltac2 use_lemma_once () :=
    let flag := { used := false } in
    fun _carrier lhs _rel => rw_lemma flag lhs.

  (* This example goes under binders to apply a rewrite only once *)
  Lemma with_env (b : bool) : forall (v : nat), (v + 2) = S (S v).
  Proof.
    rewrite_strat (topdown (tactic (use_lemma_once ()))) None.
    match! goal with
    | [ |- forall v, (2 + v) = (S (S v)) ] => id
    end.
    now reflexivity.
  Qed.

  Ltac2 failing () :=
    fun _carrier lhs _rel => exact tt; Strategy.Identity.

  (* This example goes under binders to apply a rewrite only once *)
  Lemma failure_test (b : bool) : forall (v : nat), (v + 2) = S (S v).
  Proof.
    Fail rewrite_strat (topdown (tactic (failing ()))) None.
  Abort.

End StratLtac2Tactic.
