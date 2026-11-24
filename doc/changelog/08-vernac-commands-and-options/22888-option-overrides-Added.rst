- **Added:**
  interactive tools can override flags, options and debug flags, e.g. to
  toggle :flag:`Ltac Backtrace` or :flag:`Mangle Names` from an editor:
  the overrides (``Goptions.set_option_override`` and
  ``CDebug.set_override`` in the ML API) are not part of the saved
  states, which keep the values set by the commands, and :cmd:`Test` and
  :cmd:`Print Options` show them.  Flags declared with the
  ``declare_*_option_and_ref`` functions can be overridden, other options
  must be declared ``~overridable:true`` and take their overrides into
  account themselves
  (`#22888 <https://github.com/rocq-prover/rocq/pull/22888>`_,
  by Matthieu Sozeau).
