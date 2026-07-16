#!/usr/bin/env bash

. ../template/path-init.sh

rm -rf _test
mkdir -p _test/foo/theories _test/use _test/tmp

cd _test/foo || exit 1
cat > theories/A.v <<'EOT'
Definition x := 0.
EOT
cat > _CoqProject <<'EOT'
--rocq-package foo
--package-version 1.2.3
--description "Test package"
--legacy-support
-R theories Foo
theories/A.v
EOT
cat > _CoqProject.bad <<'EOT'
--rocq-package bad
-Q theories Foo
-R theories Foo
theories/A.v
EOT
cat > _CoqProject.legacy <<'EOT'
-R theories Foo
theories/A.v
EOT
cat > _CoqProject.silent <<'EOT'
--no-rocq-package-warning
-R theories Foo
theories/A.v
EOT
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
make install DSTROOT="$PWD/../tmp"

pkgdir="$(find ../tmp -type d -name foo | head -n 1)"
test -n "$pkgdir"
test -f "$pkgdir/META"
test -f "$pkgdir/rocq.d/A.vo"
grep -q 'rocqpath = "Foo"' "$pkgdir/META"
grep -q 'directory = "."' "$pkgdir/META"
test -f "$(find ../tmp -path '*/user-contrib/Foo/A.vo' | head -n 1)"

cd .. || exit 1
mkdir -p plug/theories plug/src
cat > plug/theories/Loader.v <<'EOT'
Declare ML Module "plug.plugin".
EOT
cat > plug/src/plug.mlpack <<'EOT'
Dummy
EOT
cat > plug/src/dummy.ml <<'EOT'
let () = ()
EOT
cat > plug/_CoqProject <<'EOT'
--rocq-package plug
-Q theories Plug
-I src
theories/Loader.v
src/dummy.ml
src/plug.mlpack
EOT
(cd plug && rocq makefile -f _CoqProject -o Makefile)
grep -q 'rocqpath = "Plug"' plug/src/META.plug
grep -q 'directory = "."' plug/src/META.plug
grep -q 'requires = "plug.plugin"' plug/src/META.plug
grep -q 'package "plugin"' plug/src/META.plug

libdir="$(dirname "$pkgdir")"
cd use || exit 1
cat > B.v <<'EOT'
From Foo Require A.
Definition y := A.x.
EOT
cat > _CoqProject <<'EOT'
--rocq-package bar
-package foo
-Q . Bar
B.v
EOT

if which cygpath 2>/dev/null; then
  export OCAMLPATH="$OCAMLPATH;$(cygpath -m "$libdir")"
else
  export OCAMLPATH="$OCAMLPATH:$libdir"
fi

rocq makefile -f _CoqProject -o Makefile
grep -q 'COQMF_PACKAGES = foo' Makefile.conf
if grep -q 'rocq\.d' Makefile.conf; then
  echo 'package dependency was baked into Makefile.conf'
  exit 1
fi
make

cd ../foo || exit 1
make uninstall DSTROOT="$PWD/../tmp"
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
