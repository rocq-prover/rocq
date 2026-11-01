#!/usr/bin/env bash
# $ROCQ_PROFILE_FILE makes rocq compile write profiling to file.vo.prof.json
set -e

D=misc/tmp_profile_file_env
rm -rf "$D"
mkdir -p "$D"
printf 'Definition foo := 0.\nLemma bar : True.\nProof. exact I. Qed.\n' > "$D/a.v"

# not set: no profile file
$coqc "$D/a.v"
[ ! -e "$D/a.vo.prof.json" ]

# empty: no profile file
ROCQ_PROFILE_FILE= $coqc "$D/a.v"
[ ! -e "$D/a.vo.prof.json" ]

# set: profile file next to the output, with the profiled commands
ROCQ_PROFILE_FILE=1 $coqc "$D/a.v"
grep -q '"name": *"command"' "$D/a.vo.prof.json"

# follows -o
mkdir -p "$D/out"
ROCQ_PROFILE_FILE=1 $coqc "$D/a.v" -o "$D/out/a.vo"
[ -e "$D/out/a.vo.prof.json" ]

# an explicit -profile takes precedence
rm "$D/a.vo.prof.json"
ROCQ_PROFILE_FILE=1 $coqc -profile "$D/other.json" "$D/a.v"
[ ! -e "$D/a.vo.prof.json" ]
[ -e "$D/other.json" ]

rm -rf "$D"
