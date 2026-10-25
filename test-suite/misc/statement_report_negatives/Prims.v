(* Primitive literals for misc/statement_report_negatives.sh, compiled with
   -allow-rewrite-rules. Each declared type reaches its primitive type only
   through a rewrite rule, so only the literal needs the primitive type, which
   the kernel looks up to type it. *)

From Corelib Require Import PrimInt63 PrimFloat PrimString PrimArray.
Open Scope array_scope.

Symbol TI : Set.
Rewrite Rule TI_int := TI => int.
Definition i : TI := 0%uint63.

Symbol TF : Set.
Rewrite Rule TF_float := TF => float.
Definition f : TF := 0x1p-1%float.

Symbol TS : Set.
Rewrite Rule TS_string := TS => string.
Definition s : TS := "a"%pstring.

Symbol TA : Type.
Rewrite Rule TA_array := TA => array nat.
Definition a : TA := [| O | O |].
