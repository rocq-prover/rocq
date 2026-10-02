Declare ML Module "rocq-runtime.plugins.extraction".

Fail Extraction Language Toy.

Declare ML Module "coq-test-suite.toy_extraction".

Extraction Language Toy.

Inductive color := red | green.
Definition red' := red.

Extraction red'.
Extraction color.

Fail Separate Extraction red'.
