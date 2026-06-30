(* this test used to check that Check used to correct rule for when to
   recheck with the kernel (and avoided sending evars to the kernel),
   but now Check never rechecks with the kernel so it's always correct. *)
Goal True.
let c := open_constr:(_) in
let _ := open_constr:(c : nat) in
pose (x:=c);
pose (y := c).

Check (eq_refl : x = y).

Check (ltac:(exact_no_check (@eq_refl nat 0)) : x = y).

Check (eq_refl : x = 0).

Check (ltac:(let _ := open_constr:(eq_refl : x = 0) in
             exact_no_check (@eq_refl nat 1)) : x = 0).
Abort.
