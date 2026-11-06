(* -*- coq-prog-args: ("-w" "-notation-for-abbreviation"); -*- *)

(* [Set Suggest Proof Using] must not reset unrelated warning flags. *)
Set Suggest Proof Using.

Notation foo := nat.
