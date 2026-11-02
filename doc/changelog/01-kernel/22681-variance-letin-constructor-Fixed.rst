- **Fixed:**
  variance inference of a constructor applied in the body of a let-in of a
  constructor type, which could infer a universe irrelevant and give a proof
  of False. The type of a let-in of a constructor type or of an inductive
  arity is now inferred as the type of an argument is, so a universe which
  occurs only there is no longer irrelevant
  (`#22681 <https://github.com/rocq-prover/rocq/pull/22681>`_,
  fixes `#22675 <https://github.com/rocq-prover/rocq/issues/22675>`_,
  by Sami Jawhar).
