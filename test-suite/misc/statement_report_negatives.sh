#!/usr/bin/env bash

# rocqchk -statement-report: an axiom reached only through the hidden
# implementation of a sealed module (through a transparent constant, a
# constant or an inductive that only the implementation defines, or an axiom
# it declares), one axiom more than a clean statement, a type mismatch beside
# matches, and universe verdicts. The definitions' library is checked,
# loaded as a -norec dependency, or admitted, and the report is the same.
set -eu

D=misc/statement_report_negatives
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
cp "$D"/*.v "$D"/requests "$d/"

$coqc -noinit -Q "$d" StmtNeg "$d/Defs.v"
$coqc -noinit -Q "$d" StmtNeg "$d/Use.v"

# Flag lines and counts are left out: output-coqchk/statement_report.v pins them.
cat > "$d/expected" <<'EOF'
STATEMENT REPORT
statement sealed StmtNeg.Use.sealed StmtNeg.Use.trusted_thm match 1
axiom sealed StmtNeg.Defs.ax
statement helper StmtNeg.Use.helper - not-requested 1
axiom helper StmtNeg.Defs.ax
statement hidden_axiom StmtNeg.Use.hidden_axiom - not-requested 1
axiom hidden_axiom StmtNeg.Defs.HiddenAxiom.hidden
statement hidden_inductive StmtNeg.Use.hidden_inductive - not-requested 1
axiom hidden_inductive StmtNeg.Defs.ax
statement clean StmtNeg.Use.clean StmtNeg.Use.trusted match 1
axiom clean StmtNeg.Defs.ax
statement dirty StmtNeg.Use.dirty StmtNeg.Use.trusted match 2
axiom dirty StmtNeg.Defs.ax
axiom dirty StmtNeg.Defs.extra
statement near StmtNeg.Use.near StmtNeg.Use.trusted mismatch 1
axiom near StmtNeg.Defs.ax
statement conv StmtNeg.Use.conv StmtNeg.Use.trusted match 1
axiom conv StmtNeg.Defs.ax
statement poly_mono StmtNeg.Use.pmodel StmtNeg.Use.ptrusted universes-differ 0
statement poly_poly StmtNeg.Use.pmodel StmtNeg.Use.ptrusted_poly match 0
statement poly_constraints StmtNeg.Use.pmodel_lt StmtNeg.Use.ptrusted_lt universes-differ 0
END STATEMENT REPORT
EOF

report () {
  "$BIN"rocqchk -silent -statement-report "$d/requests" -Q "$d" StmtNeg "$@" > "$d/out.log" 2>&1 \
    || { cat "$d/out.log"; exit 1; }
  sed -n '/^STATEMENT REPORT$/,/^END STATEMENT REPORT$/p' "$d/out.log" |
    sed -e '/^flag /d' -E -e 's/^(statement( [^ ]+){5}) [0-9]+$/\1/' > "$d/report"
  diff -u "$d/expected" "$d/report"
}

report StmtNeg.Use
report -norec StmtNeg.Use
report -admit StmtNeg.Defs StmtNeg.Use
