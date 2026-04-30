From Ltac2 Require Import Ltac2.
Set Ltac2 Backtrace.

Ltac2 f () := Control.zero (Invalid_argument None).

Goal True.
Proof.
  Fail Control.plus f (fun e => Control.zero e).
  Fail Control.plus f (fun e => Control.throw e).
  Fail Control.plus_bt f (fun e bt => Control.zero_bt e bt).
  Fail Control.plus_bt f (fun e bt => Control.throw_bt e bt).
Abort.

(* based on #21312 *)
Ltac2 print_stack () := Message.print (Message.of_exninfo (Control.current_exninfo())).

Ltac2 g () := print_stack ().
Ltac2 h () := g ().

Goal True.
Proof.
  h ().
Abort.
