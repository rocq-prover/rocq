#!/usr/bin/env bash

# rocqchk must refuse a delta resolver alias that coqc never writes. For each
# case, forge.ml records one in a library compiled by coqc, and a client
# compiled against <case>/donor/Lib.v proves False from it:
# - parameter: M2.c becomes an alias of M1.c in the type of M2, where both
#   are declared-only, M1.c := true and M2.c := false.
# See misc/rocqchk_delta_alias.sh for forged aliases between definitions.

set -e

. misc/rocqchk-delta-alias/forge-lib.sh
ROOT=ForgedAliases

for case in parameter; do
  C=$D/$case
  LOG=$C/out.log
  build "$C/honest" Lib Client
  build "$C/donor" Lib Client
  rm -rf "$C/forged"
  mkdir "$C/forged"
  forge $case "$C/honest/Lib.vo" "$C/forged/Lib.vo"
  forge client "$C/donor/Client.vo" "$C/forged/Lib.vo" \
    ForgedAliases.Lib "$C/forged/Client.vo"
  accept $case "$C/honest" Lib Client
  refuse $case "Module typing error" "$C/forged" Lib Client
done
exit $fail
