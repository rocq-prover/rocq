Require Import Setoid.

From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Std.
From Ltac2 Require Import Rewrite.


Ltac2 k1 () := rewrite_strat (seqs [subterms id; choice (subterm fail) fail; fail]) None. Print Ltac2 k1.
Ltac2 k2 () := rewrite_strat (seq (seq (subterms (subterms fail)) (subterms (subterms fail))) (seq (subterms (try fail)) (subterms (repeat fail)))) None. Print Ltac2 k2.

Ltac2 mytry rewstrategy1 := rewrite_strat (choice (rewstrategy1) id) None. Print Ltac2 mytry.
Ltac2 myany rewstrategy1 := rewrite_strat (fix_ (fun fixident => try (seq rewstrategy1 fixident))) None. Print Ltac2 myany.
Ltac2 myrepeat rewstrategy1 := rewrite_strat (seq rewstrategy1 (any rewstrategy1)) None. Print Ltac2 myrepeat.
Ltac2 mybottomup rewstrategy1 := rewrite_strat (fix_ (fun fixident => seq (choice (progress (subterms fixident)) (rewstrategy1)) (try fixident))) None. Print Ltac2 mybottomup.
Ltac2 mytopdown rewstrategy1 := rewrite_strat (fix_ (fun fixident => seq (choice (rewstrategy1) (progress (subterms fixident))) (try fixident))) None. Print Ltac2 mytopdown.
Ltac2 myinnermost rewstrategy1 := rewrite_strat (fix_ (fun fixident => choice (subterm fixident) (rewstrategy1))) None. Print Ltac2 myinnermost.
Ltac2 myoutermost rewstrategy1 := rewrite_strat (fix_ (fun fixident => choice (rewstrategy1) (subterm fixident))) None. Print Ltac2 myoutermost.
