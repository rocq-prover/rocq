(* Scala 3 extraction backend: [Extract Inductive] with a match-function
   string, and [Extract Constant] on a function with real callers in the
   same file - together, the mechanism behind ExtrScalaNatInt.v (mapping
   [nat] onto Scala's native [Int]), see SCALA_EXTRACTION.md, "Extract
   Inductive with a match function".

   Two bugs this test locks in, both only ever visible to a real
   `scalac` (never to `coqc`/dry inspection alone - see
   SCALA_EXTRACTION.md's own testing-tier split):

   - Scala has no bare-juxtaposition application ([f x y]): every
     argument to the match function - here [(fO)(fS)(n)] - needs its
     own [(...)], and the *whole* application needs one more,
     unconditional pair of parens on top of that, or Scala 3's
     semicolon inference silently turns "call, call, call" into three
     unrelated statements (no error - just the wrong answer).
   - An [Extract Constant]-replaced definition ([mul] below) is called
     directly, uncast, by other code in the same file ([fact]) exactly
     as if it had its real type - so it has to be *declared* with that
     real type too, not the blanket [Any] every customized definition
     used to get regardless of whether one was available; and multiple
     such (real-typed) declarations back to back must not drift off the
     left margin (a Scala-3-only hazard: significant indentation reads
     a more-indented continuation value as an *implicit block*, which
     then swallows the next sibling declaration as part of the
     *previous* one's value instead of printing it as its own). *)

Require Import Extraction.

Extraction Language Scala.

Extract Inductive nat => "Int"
  [ "0" "((n: Int) => n + 1)" ]
  "((fO: Any => Any) => (fS: Any => Any) => (n: Int) =>
      if (n == 0) fO(()) else fS(n - 1))".

Extract Constant Nat.mul => "((n: Int) => (m: Int) => n * m)".
Extract Constant Nat.add => "((n: Int) => (m: Int) => n + m)".

Fixpoint fact (n : nat) : nat :=
  match n with
  | 0 => 1
  | S p => n * fact p
  end.

Recursive Extraction fact Nat.add Nat.mul.
