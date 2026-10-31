#!/usr/bin/env bash

# A report over every field of this sealed module must use the cached Id.Map
# index in check_closure.ml, not rescan a structure-body association list for
# each cN -> c(N-1) edge.
set -eu

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
n=1024
{
  printf 'Module Type S. Parameter out : nat. End S.\n'
  printf 'Module M : S.\nDefinition c0 : nat := O.\n'
  for ((i = 1; i <= n; ++i)); do
    printf 'Definition c%d : nat := c%d.\n' "$i" "$((i - 1))"
  done
  printf 'Definition out : nat := c%d.\nEnd M.\n' "$n"
  printf 'Definition model : nat := M.out.\n'
} > "$d/Wide.v"

$coqc -Q "$d" StmtWide "$d/Wide.v"
printf 'wide StmtWide.Wide.model -\n' > "$d/requests"
"$BIN"rocqchk -silent -statement-report "$d/requests" -Q "$d" StmtWide StmtWide.Wide > "$d/out" 2>&1
sed -n '/^STATEMENT REPORT$/,/^END STATEMENT REPORT$/p' "$d/out"
awk '$1 == "statement" && $2 == "wide" { found = 1; ok = ($6 == 0 && $7 == 0) }
     END { exit !(found && ok) }' "$d/out"
