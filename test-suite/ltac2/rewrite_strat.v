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
