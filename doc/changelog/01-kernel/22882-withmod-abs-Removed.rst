- **Removed:**
  `T with Module M := N` when `M` is not abstract (from :cmd:`Declare Module`) in `T`
  (it required `N` to be equal to the definition on `M` so was useless)
  (`#22882 <https://github.com/rocq-prover/rocq/pull/22882>`_,
  by Gaëtan Gilbert).
