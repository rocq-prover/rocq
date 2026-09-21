- **Fixed:**
  ``rocqchk`` failed with an anomaly on ``.vo`` files whose library segment
  exceeds 4 GiB of marshalled data, which OCaml writes with a different
  marshal header
  (`#22512 <https://github.com/rocq-prover/rocq/pull/22512>`_,
  fixes `#22511 <https://github.com/rocq-prover/rocq/issues/22511>`_,
  by Jason Gross).
