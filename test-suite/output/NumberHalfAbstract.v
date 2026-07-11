(* Half-abstract parsing of large nat literals:
   above the threshold, the literal is parsed to
   [of_num_little_uint (little-endian digits)] instead of either a huge
   unary numeral or a fully abstract big-endian application. *)
Check 6000.
Definition big := 6000.
Print big.
(* conversion goes through of_num_little_uint *)
Compute big - 5999.
Check (eq_refl : big = 6000).
(* hexadecimal payloads take the same path *)
Definition bigh := 0x2000.
Compute bigh - 8191.
(* below the threshold nothing changes *)
Definition small := 42.
Print small.
Set Printing All.
Print big.
