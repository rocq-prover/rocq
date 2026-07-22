#!/usr/bin/env bash

set -ex

. ../template/path-init.sh

rm -rf _test
mkdir _test
find . -maxdepth 1 -not -name . -not -name _test -exec cp -r '{}' -t _test ';'
cd _test

testdir=$PWD

# foo: a package with both findlib and legacy install
cd foo || exit 1
rocq makefile -f _CoqProject.legacy -o Makefile.legacy 2> legacy.err
grep -q 'Omitting --rocq-package is deprecated' legacy.err
rocq makefile -f _CoqProject.silent -o Makefile.silent 2> silent.err
if grep -q 'Omitting --rocq-package is deprecated' silent.err; then
  echo '--no-rocq-package-warning did not suppress the warning'
  exit 1
fi
if rocq makefile -f _CoqProject.bad -o Makefile.bad; then
  echo '--rocq-package accepted both -Q and -R'
  exit 1
fi

rocq makefile -f _CoqProject -o Makefile
grep -q 'rocqpath = "Foo"' META.foo
grep -q 'directory = "."' META.foo
grep -q 'version = "1.2.3"' META.foo
grep -q 'description = "Test package"' META.foo
make
make install DSTROOT="$testdir/tmp"

pkgdir="$(find "$testdir/tmp" -type d -name foo | head -n 1)"
libdir="$(dirname "$pkgdir")"
user_contrib_dir=$(find "$testdir/tmp" -type d -name user-contrib)
test -n "$pkgdir"
test -f "$pkgdir/META"
test -f "$pkgdir/rocq.d/A.vo"
grep -q 'rocqpath = "Foo"' "$pkgdir/META"
grep -q 'directory = "."' "$pkgdir/META"
test -f "$user_contrib_dir/Foo/A.vo"

# plug: a plugin (and Loader.v) with only findlib install
cd ../plug || exit 1
rocq makefile -f _CoqProject -o Makefile
grep -q 'rocqpath = "Plug"' src/META.plug
grep -q 'directory = "."' src/META.plug
grep -q 'requires = "plug.plugin"' src/META.plug
grep -q 'package "plugin"' src/META.plug
make
make install DSTROOT="$testdir/tmp"

# installed in findlib but not user-contrib
test "$libdir/plug/rocq.d/Loader.vo" = "$(find "$testdir/tmp" -name Loader.vo)"

cd ../use || exit 1

if which cygpath 2>/dev/null; then
  export OCAMLPATH="$(cygpath -m "$libdir");$OCAMLPATH"
else
  export OCAMLPATH="$libdir:$OCAMLPATH"
fi

rocq makefile -f _CoqProject -o Makefile
grep -q 'COQMF_PACKAGES = foo plug' Makefile.conf ||
  grep -q 'COQMF_PACKAGES = plug foo' Makefile.conf

if grep -q 'rocq\.d' Makefile.conf; then
  echo 'package dependency was baked into Makefile.conf'
  exit 1
fi
make
test -e B.vo

cd ../foo || exit 1
make uninstall DSTROOT="$testdir/tmp"
test ! -e "$pkgdir/META"
test ! -d "$pkgdir/rocq.d"
test -z "$(find ../tmp -path '*/user-contrib/Foo/A.vo' | head -n 1)"

echo 'Print LoadPath.' > Empty.v

# -native-compiler no: with -boot, native compilation would additionally
# require -nI pointing to the kernel, which is beside the point here
rocq c -native-compiler no -boot -noinit Empty.v

if rocq c -native-compiler no -boot Empty.v; then
  >&2 echo -boot without -noinit should have failed
  exit 1
fi

rocq c -native-compiler no -boot -package rocq-core Empty.v > loadpaths.package
grep -q "Corelib" loadpaths.package
grep -qv "user-contrib" loadpaths.package
grep -qv "Ltac2" loadpaths.package

rocq c Empty.v > loadpaths.legacy
grep -q "Corelib" loadpaths.legacy
grep -q "user-contrib" loadpaths.legacy
grep -q "Ltac2" loadpaths.legacy
