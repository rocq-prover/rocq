Declare ML Module "unsafe_cast.plugin".

(* The evaluator is an identity stub with #20503's interface. The cast handler
   explicitly resumes ordinary conversion; no erasure behavior is simulated. *)
Definition erased := eq_refl <:["test.erase"] (true = negb false).
Print erased.
Print Assumptions erased.

(* Source evars are inferred through the target preparation hook. *)
Check erased : true = true.
Fail Check (eq_refl <:["test.erase"] (true = false)).

Lemma erased_opaque : true = negb false.
Proof. exact (eq_refl <:["test.erase"] (true = negb false)). Qed.
Print Assumptions erased_opaque.
