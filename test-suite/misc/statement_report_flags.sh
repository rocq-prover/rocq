#!/usr/bin/env bash

# One statement for every per-object relaxed typing flag, including a flag
# reached through a sealed implementation and an opaque hidden proof. The
# second run sends that opaque proof to -j workers.
set -eu

D=misc/statement_report_negatives
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
cp "$D/Flags.v" "$D/flag_requests" "$d/"

$coqc -Q "$d" StmtNeg "$d/Flags.v"

report () {
  "$BIN"rocqchk -silent -statement-report "$d/flag_requests" -Q "$d" StmtNeg "$@" > "$d/out" 2>&1
  sed -n '/^STATEMENT REPORT$/,/^END STATEMENT REPORT$/p' "$d/out"
  grep -q '^flag guard unsafe-fixpoint StmtNeg.Flags.g$' "$d/out"
  grep -q '^flag tit type-in-type StmtNeg.Flags.tt_T$' "$d/out"
  grep -q '^flag pos assumed-positive StmtNeg.Flags.Bad$' "$d/out"
  grep -q '^flag uip uip StmtNeg.Flags.UIP.seq$' "$d/out"
  grep -q '^flag hidden_flag unsafe-fixpoint StmtNeg.Flags.HG.loop$' "$d/out"
  grep -q '^axiom opaque_hidden StmtNeg.Flags.oax$' "$d/out"
  awk '
    $1 == "statement" { if (seen) { if (a != ac || f != fc) exit 1 }; seen = 1; a = f = 0; ac = $6; fc = $7 }
    $1 == "axiom" { ++a }
    $1 == "flag" { ++f }
    END { exit !(seen && a == ac && f == fc) }
  ' "$d/out"
}

report -norec StmtNeg.Flags
