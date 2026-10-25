#!/usr/bin/env bash

# Deliberately fault after the report start marker. The checker must retain the
# underlying successful-check exit status, warn, and omit END STATEMENT REPORT
# so a downstream parser cannot treat the partial stream as evidence.
set -eu

D=misc/statement_report_view
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
cp "$D/View.v" "$d/"

$coqc -Q "$d" StmtView "$d/View.v"
printf 'boom StmtView.View.Impl.boom -\n' > "$d/requests"
if ! env COQ_TEST_SUITE_STATEMENT_REPORT_FAILURE=1 \
  "$BIN"rocqchk -silent -statement-report "$d/requests" -Q "$d" StmtView StmtView.View > "$d/out" 2>&1; then
  exit 1
fi
grep -q '^STATEMENT REPORT$' "$d/out"
if grep -q '^END STATEMENT REPORT$' "$d/out"; then
  exit 1
fi
grep -q '^Warning: Statement report stopped:.*test statement-report failure' "$d/out"
