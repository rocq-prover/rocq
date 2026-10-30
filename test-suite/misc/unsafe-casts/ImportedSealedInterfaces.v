From UnsafeCasts Require Import SealedInterfaces.

(* The same interface/implementation dependencies must survive .vo reload. *)
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
