#!/usr/bin/env bash

# The deprecated-coq-env-var warning is emitted while computing load paths,
# before the initial state is built, so -w had no effect on it. Check that it
# can be silenced, and that it is still emitted when it is not.

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

set -e

TMP=`mktemp -d`
cd $TMP

cat > silence.v <<EOT
Definition x := 1.
EOT

export COQPATH="$TMP"

set +e

N=`rocq c -q silence.v 2>&1 | grep -c "Deprecated environment variable"`
if [ $N -ne 1 ]; then
  echo "the deprecated-coq-env-var warning is not emitted without -w"
  rocq c -q silence.v
  rm -rf $TMP
  exit 1
fi

N=`rocq c -q -w -deprecated-coq-env-var silence.v 2>&1 | grep -c "Deprecated environment variable"`
if [ $N -ne 0 ]; then
  echo "the deprecated-coq-env-var warning is not silenced by -w"
  rocq c -q -w -deprecated-coq-env-var silence.v
  rm -rf $TMP
  exit 1
fi

rm -rf $TMP
exit 0
