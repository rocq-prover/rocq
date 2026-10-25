#!/usr/bin/env bash

# rocqchk -statement-report's type verdict is the sealing it stands for: for
# each row, [Definition f := <model>] ([Polymorphic] for a polymorphic
# statement), the spelling a grader's checker uses, is compiled by coqc in a
# module sealed by the row's module type. [match] must be accepted, and
# [mismatch] and [universes-differ] refused. A row marked [under] has a model
# whose universe context elaboration can minimize: the report answers
# [universes-differ] for it whatever the sealing does, so that it never says
# [match] for a definition the sealing refuses.
set -eu

D=misc/statement_report_sealing
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
cp "$D/Defs.v" "$d/"

$coqc -noinit -Q "$d" StmtSeal "$d/Defs.v"

# <row>|<model>|<expected verdict>|[Polymorphic]|[under]
rows='same|m_same|match||
set_type|m_set|match||
prop_type|m_prop|match||
indep|m_indep|match||
incons|m_incons|universes-differ||
qsort|m_qsort|match||
qsort_lt|m_qsort_lt|universes-differ||
alg|m_alg|universes-differ||
poly_mono|m_poly|match||
poly_mono_lt|m_poly_lt|universes-differ||
poly_mono_le|m_two|universes-differ||under
poly_poly|m_poly|match|Polymorphic|
poly_lt|m_poly_lt|universes-differ|Polymorphic|
poly_strong|m_poly_le|universes-differ|Polymorphic|under
poly_le_le|m_poly_le|universes-differ|Polymorphic|under
poly_univ|m_poly_univ|universes-differ|Polymorphic|
poly_sort|m_poly_sort|universes-differ|Polymorphic|under
mono_poly|m_set|match|Polymorphic|
different|m_fun|mismatch||
binder|m_binder|mismatch||'

: > "$d/requests"
while IFS='|' read -r row model expected poly under; do
  printf '%s StmtSeal.Defs.%s StmtSeal.Defs.t_%s\n' "$row" "$model" "$row" >> "$d/requests"
  printf 'Require StmtSeal.Defs.\nModule X <: StmtSeal.Defs.S_%s.\n  %sDefinition f := StmtSeal.Defs.%s.\nEnd X.\n' \
    "$row" "${poly:+$poly }" "$model" > "$d/Seal_$row.v"
done <<< "$rows"

"$BIN"rocqchk -silent -statement-report "$d/requests" -Q "$d" StmtSeal StmtSeal.Defs > "$d/out" 2>&1 \
  || { cat "$d/out"; exit 1; }
sed -n 's/^statement \([^ ]*\) [^ ]* [^ ]* \([^ ]*\) .*/\1 \2/p' "$d/out" > "$d/verdicts"

# Sealing is refused by a signature mismatch, or by the anomaly that the
# elaborator's universe inference raises when it must make an algebraic
# universe equal to a level (engine/univSubst.ml's [enforce_eq]).
fail=0
printf '%-13s %-17s %-17s %s\n' row expected report sealing
while IFS='|' read -r row model expected poly under; do
  verdict=$(sed -n "s/^$row //p" "$d/verdicts")
  if $coqc -noinit -Q "$d" StmtSeal "$d/Seal_$row.v" < /dev/null > "$d/seal_$row.log" 2>&1; then
    sealing=accepted
  elif grep -q -e 'Signature components for field f do not match' \
         -e 'A universe comparison can only happen between variables' "$d/seal_$row.log"; then
    sealing=refused
  else
    sealing=error; cat "$d/seal_$row.log"
  fi
  printf '%-13s %-17s %-17s %s%s\n' "$row" "$expected" "$verdict" "$sealing" "${under:+ ($under)}"
  [ "$verdict" = "$expected" ] || fail=1
  case "$verdict,$sealing,$under" in
    match,accepted, | mismatch,refused, | universes-differ,refused,) ;;
    universes-differ,accepted,under | universes-differ,refused,under) ;;
    *) fail=1 ;;
  esac
done <<< "$rows"
exit $fail
