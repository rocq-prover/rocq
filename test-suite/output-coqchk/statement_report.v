(* -*- coqchk-prog-args: ("-statement-report" "output-coqchk/statement_report.req") -*- *)

(* rocqchk -statement-report prints, for each request, whether the model
   constant has the trusted constant's type and the axioms its closure uses:
   here [ax], reached through the opaque [model] and the transparent
   [via_ax]. [trusted_other] is a statement [model] does not prove. *)

Axiom ax : nat.
Definition via_ax : nat := ax.
Lemma model : via_ax = via_ax. Proof. exact eq_refl. Qed.
Parameter trusted : via_ax = via_ax.
Parameter trusted_other : 0 = 0.
