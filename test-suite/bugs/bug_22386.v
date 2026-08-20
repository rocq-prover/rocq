CoInductive Stream : Type := next : Stream -> Stream.
Inductive Empty : Type := wrap : Empty -> Empty.

Fail
Definition cycle : Empty :=
  let actual := Empty in
  let decoy := Stream in
  cofix recur : actual := wrap recur.

(*
Fixpoint absurd (x : Empty) : False :=
  match x with wrap y => absurd y end.

Definition contradiction : False := absurd cycle.
Print Assumptions contradiction.
*)
