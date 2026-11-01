- **Added:**
  environment variables :ref:`ROCQ_TIME_FILE <ROCQ_TIME_FILE>` and
  :ref:`ROCQ_PROFILE_FILE <ROCQ_PROFILE_FILE>`, which make ``rocq compile``
  output per-command timing to :n:`file.v.timing` and profiling to
  :n:`file.vo.prof.json` (as ``rocq makefile`` does with ``TIMING=1`` and
  ``PROFILING=1``), for build systems which cannot pass per-file options,
  such as Dune
  (`#22694 <https://github.com/rocq-prover/rocq/pull/22694>`_,
  by Pierre-Marie Pédrot).
