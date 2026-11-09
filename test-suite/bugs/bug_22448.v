Notation "'start' τ1 -> .. -> τn -> τm -> A" :=
  (cons τ1 ( .. ( cons τn (cons τm (cons A nil))) .. ))
  (at level 20, τ1, τn, τm, A at level 9).

Check eq_refl : start 1 -> 2 -> 3 = cons 1 (cons 2 (cons 3 nil)).
Check eq_refl : start 1 -> 2 -> 3 -> 4 = cons 1 (cons 2 (cons 3 (cons 4 nil))).
Check eq_refl : start 1 -> 2 -> 3 -> 4 -> 5 = cons 1 (cons 2 (cons 3 (cons 4 (cons 5 nil)))).
