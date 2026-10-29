Declare ML Module "unsafe_cast.plugin".

(* Unlike Main.v's sealed-module test, the cast is in the exposed type. *)
Module Type Signature.
  Parameter value : (nat <:["test.vm-lhs"] Set).
End Signature.
Module InterfaceOnly : Signature.
  Definition value := 0.
End InterfaceOnly.
Definition interface_use : nat := InterfaceOnly.value.

(* Recovering the implementation must not replace the exposed type, and
   inspecting the exposed type must not hide the implementation's cast. *)
Module Mixed : Signature.
  Definition value := 0 <:["test.accept"] nat.
End Mixed.
Definition mixed_use : nat := Mixed.value.

(* The same lookup also hides older kinds of public-type dependencies. *)
Module AxiomType.
  Axiom ax : nat.
  Definition ty := (fun _ : nat => nat) ax.
  Module Type Signature. Parameter value : ty. End Signature.
  Module Sealed : Signature. Definition value := 0. End Sealed.
End AxiomType.

Module Type FlaggedSignature.
  Unset Universe Checking.
  Parameter value : nat.
  Set Universe Checking.
End FlaggedSignature.
Module Flagged : FlaggedSignature. Definition value := 0. End Flagged.

Print Assumptions InterfaceOnly.value.
Print Assumptions interface_use.
Print Assumptions Mixed.value.
Print Assumptions mixed_use.
Print Assumptions AxiomType.Sealed.value.
Print Assumptions Flagged.value.
