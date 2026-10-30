Inductive Rec := { unrec : Rec }.

Definition f : Rec -> False.
Proof.
  fix rec 1.
  apply id.
  exact (fun x => rec (unrec x)).
Defined.

Eval vm_compute in f.
Eval native_compute in f.
