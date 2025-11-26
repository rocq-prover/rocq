Require Import Ltac2.Ltac2.
Import Printf.

(** basic test, we also check that the backtrace isn't forgotten when
    using the custom printer *)

Set Ltac2 Backtrace.

Ltac2 foo () := Control.zero (Tactic_failure (Some (Message.of_string "hello"))).

Fail Ltac2 Eval foo ().

Unset Ltac2 Backtrace.

(** Test printing constr even though we have a bad evar map *)

Ltac2 Type exn ::= [ WithTerm (constr) ].

Ltac2 bar () :=
  let c := open_constr:(_ :> nat) in
  Control.zero (WithTerm c).

(* default printer doesn't have the evar map but doesn't fail *)
Fail Ltac2 Eval bar ().

Ltac2 Set Control.print_exn := fun e =>
  match e with
  |  WithTerm c => Some (fprintf "test %t" c)
  | _ => None
  end.

(* custom printer also doesn't have the evar map but doesn't fail *)
Fail Ltac2 Eval bar ().

(** Test custom printer producing an error *)
Ltac2 Set Control.print_exn := fun _ => Control.throw Assertion_failure.

Fail Ltac2 Eval foo ().
