- **Changed:**
  record syntax is now allowed for records with anonymous fields, producing holes for the non provided fields
  (anonymous fields cannot be provided since they have no name).
  Note that records without anonymous fields already produced holes for non provided fields instead of producing an error,
  so `{[ x := 0 |}` now works to produce a value of either `Record R := { x : nat; y : P x }` or `Record R := { x : nat; _ : P x }`
  where previously only the former would work
  (`#22307 <https://github.com/rocq-prover/rocq/pull/22307>`_,
  by Gaëtan Gilbert).
