- **Changed:**
  tactics such as :tacn:`induction` find eliminators (like `nat_rect`)
  through the :cmd:`Register Scheme` table (which is automatically populated by :cmd:`Scheme` and automatic scheme declarations)
  instead of by name (the lookup by name remains for now for backward compatibility)
  (`#20614 <https://github.com/rocq-prover/rocq/pull/20614>`_,
  by Gaëtan Gilbert).
