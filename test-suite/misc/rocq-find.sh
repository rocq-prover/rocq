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
