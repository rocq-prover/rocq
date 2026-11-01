#!/usr/bin/env bash
# $ROCQ_TIME_FILE makes rocq compile write per-command timing to file.v.timing
set -e

D=misc/tmp_time_file_env
rm -rf "$D"
mkdir -p "$D"
printf 'Definition foo := 0.\nLemma bar : True.\nProof. exact I. Qed.\n' > "$D/a.v"

# not set: no timing file
$coqc "$D/a.v"
[ ! -e "$D/a.v.timing" ]

# empty: no timing file
ROCQ_TIME_FILE= $coqc "$D/a.v"
[ ! -e "$D/a.v.timing" ]

# set: timing file next to the source, one line per command
ROCQ_TIME_FILE=1 $coqc "$D/a.v"
[ "$(grep -c '^Chars ' "$D/a.v.timing")" = 5 ]

# an explicit -time-file takes precedence
rm "$D/a.v.timing"
ROCQ_TIME_FILE=1 $coqc -time-file "$D/other.timing" "$D/a.v"
[ ! -e "$D/a.v.timing" ]
[ -e "$D/other.timing" ]

rm -rf "$D"
