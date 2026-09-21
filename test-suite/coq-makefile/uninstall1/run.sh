#!/usr/bin/env bash

. ../template/init.sh

dst="$PWD/tmp"
if command -v cygpath >/dev/null 2>&1; then
  dst=$(cygpath -m "$dst")
fi

rocq makefile -f _CoqProject -o Makefile
cat Makefile.conf
make
make html mlihtml
make install DSTROOT="$dst"
make install-doc DSTROOT="$dst"
make uninstall DSTROOT="$dst"
make uninstall-doc DSTROOT="$dst"
#make debug
(
  while IFS= read -r -d '' d
  do
    pushd "$d" >/dev/null && find . && popd >/dev/null
  done < <(find tmp \( -name user-contrib -o -name coq-test-suite \) -print0)
) | sort -u > actual
sort -u > desired <<EOT
.
./test
./test/sub
EOT
(rocq -config | grep -q "NATIVE_COMPILER_DEFAULT=yes") || sed -i.bak '/test/d' desired
exec diff -u desired actual
