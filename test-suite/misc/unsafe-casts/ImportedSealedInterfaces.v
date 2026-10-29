From UnsafeCasts Require Import SealedInterfaces.

(* The same interface/implementation dependencies must survive .vo reload. *)
Print Assumptions InterfaceOnly.value.
Print Assumptions interface_use.
Print Assumptions Mixed.value.
Print Assumptions mixed_use.
Print Assumptions AxiomType.Sealed.value.
Print Assumptions Flagged.value.
