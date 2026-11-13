# Shell functions for the misc/rocqchk_*.sh tests that source this file to
# forge .vo files with forge.ml. A test sources it from test-suite/, then
# sets ROOT, the logical name of its libraries, and LOG, the file for
# rocqchk's output.

D=misc/rocqchk-delta-alias
fail=0

forge() { ocaml "$D/forge.ml" "$@"; }

# build <dir> <file>...: compile <dir>/<file>.v, in that order, after
# removing the compiled files of an earlier run.
build() {
  local dir=$1 f
  shift
  rm -f "$dir"/*.vo "$dir"/*.vok "$dir"/*.vos "$dir"/*.glob
  for f in "$@"; do
    $coqc -noinit -R "$dir" "$ROOT" "$dir/$f.v"
  done
}

# compile <dir> <file>...: build, and make <dir>/forged an empty directory.
compile() {
  rm -rf "$1/forged"
  build "$@"
  mkdir "$1/forged"
}

# chk <dir> <library>...: rocqchk on $ROOT.<library>... in <dir>.
chk() {
  local dir=$1 libs=() l
  shift
  for l in "$@"; do libs+=("$ROOT.$l"); done
  "$BIN"rocqchk -R "$dir" "$ROOT" "${libs[@]}" > "$LOG" 2>&1
}

# accept <case> <dir> <library>...: rocqchk must accept the libraries.
accept() {
  local name=$1
  shift
  if ! chk "$@"; then
    echo "rocqchk refused the files of case $name"
    cat "$LOG"
    fail=1
  fi
}

# refuse <case> <error> <dir> <library>...: rocqchk must refuse the
# libraries with an error that the extended regular expression <error>
# matches.
refuse() {
  local name=$1 error=$2
  shift 2
  if chk "$@"; then
    echo "rocqchk accepted the forged files of case $name"
    cat "$LOG"
    fail=1
  elif ! grep -Eq "$error" "$LOG"; then
    echo "unexpected rocqchk failure for the forged files of case $name"
    cat "$LOG"
    fail=1
  fi
}
