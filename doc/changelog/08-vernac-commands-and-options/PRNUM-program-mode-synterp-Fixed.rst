- **Fixed:**
  :flag:`Program Mode` is now set at synterp time, as the default value of the
  :attr:`program` attribute is read when parsing the attributes of commands
  defined by plugins (``VERNAC EXTEND``), which happens at synterp time: the
  flag was ignored by such commands in document managers that synterp sentences
  ahead of their interpretation, such as VsRocq
  (`#PRNUM <https://github.com/rocq-prover/rocq/pull/PRNUM>`_,
  by Matthieu Sozeau).
