- **Added:**
  Named unsafe casts, written ``term <:["plugin.cast-id"] type``, with
  plugin-registered kernel checkers that explicitly choose their conversion
  procedure. Uses are tracked transitively by :cmd:`Print Assumptions`,
  including in opaque proofs. Plugins may provide source and target
  preparation callbacks to assist elaboration. These callbacks extend the
  trusted computing base; see :ref:`type-cast`.
