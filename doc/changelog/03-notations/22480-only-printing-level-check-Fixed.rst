- **Fixed:**
  A :cmd:`Notation` that adds no parsing rule, such as an ``only printing``
  one, no longer has to be declared at the level recorded for its notation
  string, which had forced an import order on developments mixing VST with
  mathcomp. The mismatch is now reported by the new
  :warn:`notation-incompatible-level` warning. Two parsing rules for the same
  string at incompatible levels remain an error
  (`#22480 <https://github.com/rocq-prover/rocq/pull/22480>`_,
  fixes `#12465 <https://github.com/rocq-prover/rocq/issues/12465>`_
  and `#12589 <https://github.com/rocq-prover/rocq/issues/12589>`_,
  by remix7531).
