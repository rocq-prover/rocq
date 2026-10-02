(* Scala 3 extraction backend: [Set Extraction Scala Package] and the
   [object] wrapper every file gets regardless (see SCALA_EXTRACTION.md,
   "One object per file, and packages"). The filename-derived object
   name (the other half of that section) isn't exercised here: a named
   target file (`Extraction "Foo" ...`) writes straight to disk instead
   of stdout, so there is nothing for this stdout-diff mechanism to
   check - see run_scala_extraction_tests.sh's dedicated self-test for
   that instead. *)

Require Import Extraction.

Extraction Language Scala.

Definition answer : nat := 42.

(* No package set yet: only the wrapping object appears. *)
Recursive Extraction answer.

Set Extraction Scala Package "com.foo.bar".

(* A valid package prints a [package com.foo.bar] line before the
   object. *)
Recursive Extraction answer.

(* Rejected outright, instead of emitting Scala that doesn't compile. *)
Fail Set Extraction Scala Package "1bad.pkg".
Fail Set Extraction Scala Package "bad name".

Unset Extraction Scala Package.

(* Back to no package line, same as the very first extraction above. *)
Recursive Extraction answer.
