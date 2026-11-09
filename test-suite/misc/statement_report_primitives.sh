#!/usr/bin/env bash

# Each primitive literal gets its type only through the retroknowledge entry.
set -eu

D=misc/statement_report_negatives
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
cp "$D/Prims.v" "$D/prim_requests" "$d/"

$coqc -allow-rewrite-rules -Q "$d" StmtNeg "$d/Prims.v"
"$BIN"rocqchk -silent -statement-report "$d/prim_requests" -Q "$d" StmtNeg -norec StmtNeg.Prims > "$d/out" 2>&1
sed -n '/^STATEMENT REPORT$/,/^END STATEMENT REPORT$/p' "$d/out"
cat > "$d/expected" <<'EOF'
STATEMENT REPORT
statement int StmtNeg.Prims.i - not-requested 2
axiom int Corelib.Numbers.Cyclic.Int63.PrimInt63.int
axiom int StmtNeg.Prims.TI
statement float StmtNeg.Prims.f - not-requested 2
axiom float Corelib.Floats.PrimFloat.float
axiom float StmtNeg.Prims.TF
statement string StmtNeg.Prims.s - not-requested 2
axiom string Corelib.Strings.PrimString.string
axiom string StmtNeg.Prims.TS
statement array StmtNeg.Prims.a - not-requested 2
axiom array Corelib.Array.PrimArray.array
axiom array StmtNeg.Prims.TA
END STATEMENT REPORT
EOF
sed -n '/^STATEMENT REPORT$/,/^END STATEMENT REPORT$/p' "$d/out" |
  sed -e '/^flag /d' -E -e 's/^(statement( [^ ]+){5}) [0-9]+$/\1/' > "$d/report"
diff -u "$d/expected" "$d/report"
