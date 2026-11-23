(* -*- coq-prog-args: ("-noinit" "-allow-rewrite-rules"); -*- *)

(* A module alias and an Include copy a symbol. Strengthening makes each
   copy a definition of the symbol, under the symbol's canonical name
   (Modops.strengthen_const), so rocqchk must accept the copies as coqc
   does. The symbol has no rewrite rule: coqc fails on an anomaly when it
   copies a module that declares one. *)

Inductive unit : Set := tt.

Module F.
  Symbol s : unit.
End F.

Module G := F.

Module H.
  Include F.
End H.
