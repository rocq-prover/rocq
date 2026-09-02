- **Fixed:**
  ``rocqchk`` now validates the marshalled data of every library named on the
  command line, whatever the order of the ``-norec`` arguments; a library that
  happened to be interned first as a dependency of another explicitly named one
  was read without validation and without checking its recorded checksums
  (`#22363 <https://github.com/rocq-prover/rocq/pull/22363>`_,
  fixes `#22362 <https://github.com/rocq-prover/rocq/issues/22362>`_,
  by Jason Gross).
