#!/usr/bin/env bash

set -euo pipefail
export LC_ALL=C

ROCQ="${BIN}rocq"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

LIB="$TMP/lib"
mkdir -p "$LIB/foo" "$LIB/bar" "$LIB/rocq-runtime"

cat > "$LIB/foo/META" <<'EOT'
directory = "."
rocqpath = "Foo"
requires = "bar foo.plugin"

package "plugin" (
  directory = "plugin"
)
EOT

cat > "$LIB/bar/META" <<'EOT'
directory = "."
rocqpath = "Bar"
EOT

# rocq find filters out static toplevel libraries, so provide the package
# queried by the implementation while keeping the test findlib root isolated.
cat > "$LIB/rocq-runtime/META" <<'EOT'
directory = "."

package "toplevel" (
  directory = "."
)
EOT

if command -v cygpath >/dev/null 2>&1; then
  FINDLIB_LIB="$(cygpath -m "$LIB")"
else
  FINDLIB_LIB="$LIB"
fi

cat > "$TMP/findlib.conf" <<EOT
destdir="$FINDLIB_LIB"
path="$FINDLIB_LIB"
ocamlc="ocamlc"
ocamlopt="ocamlopt"
ocamldep="ocamldep"
ocamldoc="ocamldoc"
EOT

run_rocq_find() {
  OCAMLFIND_CONF="$TMP/findlib.conf" OCAMLPATH= "$ROCQ" find "$@"
}

# The fake packages contain only META files; rocq find should only inspect
# findlib metadata and should not require any actual theory directory.
test ! -e "$LIB/foo/rocq.d"
test ! -e "$LIB/bar/rocq.d"

run_rocq_find | sort > "$TMP/find.out"
cat > "$TMP/find.expected" <<EOT
$FINDLIB_LIB/bar/rocq.d Bar
$FINDLIB_LIB/foo/rocq.d Foo
EOT
diff -u "$TMP/find.expected" "$TMP/find.out"

run_rocq_find foo | sort > "$TMP/find-foo.out"
cat > "$TMP/find-foo.expected" <<EOT
$FINDLIB_LIB/bar/rocq.d Bar
$FINDLIB_LIB/foo/rocq.d Foo
EOT
diff -u "$TMP/find-foo.expected" "$TMP/find-foo.out"

run_rocq_find -Q -I foo | sort > "$TMP/find-foo-flags.out"
cat > "$TMP/find-foo-flags.expected" <<EOT
-I '$FINDLIB_LIB/foo'
-Q '$FINDLIB_LIB/bar/rocq.d' Bar
-Q '$FINDLIB_LIB/foo/rocq.d' Foo
EOT
diff -u "$TMP/find-foo-flags.expected" "$TMP/find-foo-flags.out"

# Package arguments are resolved when a document is initialized.  Check that
# this still installs the package and its transitive dependencies.
rm -rf "$LIB/rocq-runtime"
mkdir -p "$LIB/foo/rocq.d" "$LIB/bar/rocq.d"

cat > "$LIB/bar/rocq.d/BarValue.v" <<'EOT'
Axiom answer : Type.
EOT

$coqc -boot -noinit -Q "$LIB/bar/rocq.d" Bar \
  "$LIB/bar/rocq.d/BarValue.v"

cat > "$LIB/foo/rocq.d/FooValue.v" <<'EOT'
From Bar Require Import BarValue.
Definition answer := BarValue.answer.
EOT

$coqc -boot -noinit \
  -Q "$LIB/bar/rocq.d" Bar \
  -Q "$LIB/foo/rocq.d" Foo \
  "$LIB/foo/rocq.d/FooValue.v"

cat > "$TMP/client.v" <<'EOT'
From Foo Require Import FooValue.
Check FooValue.answer.
EOT

PACKAGE_OCAMLPATH="$FINDLIB_LIB${FINDLIB_SEP:-:}${OCAMLPATH:-}"
OCAMLPATH="$PACKAGE_OCAMLPATH" \
  $coqc -boot -noinit -package foo "$TMP/client.v"

if OCAMLPATH="$PACKAGE_OCAMLPATH" \
  $coqc -boot -noinit \
  -package missing-package "$TMP/client.v" \
  >"$TMP/missing.out" 2>&1; then
  echo "rocq c unexpectedly accepted a missing package" >&2
  exit 1
fi

grep -q "Failed to locate package missing-package" "$TMP/missing.out"
