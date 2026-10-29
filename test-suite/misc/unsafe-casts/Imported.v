From UnsafeCasts Require Import Main.

(* The cast identifiers and opaque proof dependencies survive a .vo reload. *)
Definition imported := opaque_direct.
Print Assumptions imported.
Print Assumptions type_only.
Print Assumptions arity_cast.
Print Assumptions Sealed.proof.
Print Assumptions unsafe_false.
Print Assumptions ordinary.

From UnsafeCasts Require Import Erasure.
Definition imported_erasure := erased_opaque.
Print Assumptions imported_erasure.
