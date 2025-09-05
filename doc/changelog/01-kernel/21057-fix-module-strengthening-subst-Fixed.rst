- **Fixed:**
  substitution of functor delta-resolvers when strengthening.
  The previous code was only substituting the inner delta resolvers
  and ignoring the codomain of functors. In particular this was generating
  ill-formed constants whose canonical component was pointing to a bound name
  that did not exist in the global environment, leading to an inconsistency
  (`#21057 <https://github.com/rocq-prover/rocq/pull/21057>`_,
  fixes `#21051 <https://github.com/rocq-prover/rocq/issues/21051>`_,
  by Pierre-Marie Pédrot).
