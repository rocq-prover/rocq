#!/bin/sh

set -e

export PATH="$BIN:$PATH"

cd misc
rm -rf load-succeed/
mkdir load-succeed
cd load-succeed

cat > toload.v <<'EOF'
Definition before_succeed := 0.
Succeed Example succeeds : True := I.
Definition after_succeed := S before_succeed.
EOF

echo 'Load "toload.v". Eval cbv in after_succeed.' > main.v

rocq c main.v
test -e main.vo
