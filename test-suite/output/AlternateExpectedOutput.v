(* Self-test for the alternative-expected-output mechanism of the output
   test harness (see test-suite/Makefile, diff_against_candidates).

   The produced output below is deterministic. The primary reference
   AlternateExpectedOutput.out is deliberately NOT equal to it, while the
   variant AlternateExpectedOutput.out.variant-accepted is. The test must
   therefore pass by matching the variant, exercising the candidate loop
   end to end. *)
Check tt.
