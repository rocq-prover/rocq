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

(* Equal after erasing casts is not enough to deduplicate the two types. *)
Module BothTypes : Signature.
  Definition value : (nat <:["test.accept"] Set) := 0.
End BothTypes.
Definition both_types_use : nat := BothTypes.value.

(* Manifest signature definitions must not conceal implementation bodies,
   even though the exposed declaration already has a body. Repeated markers
   in bodies and types must still be reported only once per declaration. *)
Module Type ManifestSignature.
  Definition value : (nat <:["test.vm-lhs"] Set) := 0 <:["test.vm-lhs"] nat.
End ManifestSignature.
Module Manifest : ManifestSignature.
  Definition value : (nat <:["test.accept"] Set) := 0 <:["test.accept"] nat.
End Manifest.
Definition manifest_use : nat := Manifest.value.

Module Type Empty. End Empty.
Module EmptyImpl. End EmptyImpl.
Module Functor (X : Empty) : Signature.
  Definition value := 0 <:["test.accept"] nat.
End Functor.
Module Applied := Functor EmptyImpl.
Module Alias := Applied.

(* Recover opaque proofs and hidden axioms as well as transparent bodies. *)
Module Type OpaqueSignature.
  Lemma value : True. Proof. exact I. Qed.
End OpaqueSignature.
Module OpaqueImplementation : OpaqueSignature.
  Axiom hidden : True.
  Lemma value : True. Proof. exact hidden. Qed.
End OpaqueImplementation.

(* A genuinely abstract field must still be classified as an axiom. *)
Declare Module Abstract : Signature.

(* Union disabled checks; neither descriptor alone has both flags. *)
Module Type GuardedSignature.
  Unset Guard Checking.
  Parameter value : nat.
  Set Guard Checking.
End GuardedSignature.
Module SplitFlags : GuardedSignature.
  #[bypass_check(universes=yes)] Definition value := 0.
End SplitFlags.

Print Assumptions InterfaceOnly.value.
Print Assumptions interface_use.
Print Assumptions Mixed.value.
Print Assumptions mixed_use.
Print Assumptions AxiomType.Sealed.value.
Print Assumptions Flagged.value.
Print Assumptions BothTypes.value.
Print Assumptions both_types_use.
Print Assumptions Manifest.value.
Print Assumptions manifest_use.
Print Assumptions Applied.value.
Print Assumptions Alias.value.
Print Assumptions OpaqueImplementation.value.
Print Opaque Dependencies OpaqueImplementation.value.
Print Assumptions Abstract.value.
Print Assumptions SplitFlags.value.
Set Printing All Assumptions.
Print Assumptions Flagged.value.
Print Assumptions SplitFlags.value.
Unset Printing All Assumptions.
