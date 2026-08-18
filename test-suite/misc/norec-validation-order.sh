#!/usr/bin/env bash

# A library named explicitly on the rocqchk command line must be validated when
# it is read, whatever the order of the -norec arguments. See #22362.

set -e

D=misc/norec-validation-order

rm -f "$D"/*.vo "$D"/*.vok "$D"/*.vos "$D"/*.glob "$D"/out.log

$coqc -R "$D" NorecOrder "$D/B.v"
$coqc -R "$D" NorecOrder "$D/A.v"

# Invalidate the checksum recorded for the "library" segment of B.vo. The
# marshalled data itself is untouched, so reading B.vo without validation still
# succeeds; validating it reports a corrupted file.
ocaml "$D/corrupt.ml" "$D/B.vo" library

# NorecOrder.B is a dependency of NorecOrder.A, so in one of the two orders
# below it used to be interned as a dependency and read without validation.
for args in "-norec NorecOrder.A -norec NorecOrder.B" \
            "-norec NorecOrder.B -norec NorecOrder.A"; do
  if "$BIN"rocqchk -R "$D" NorecOrder $args > "$D/out.log" 2>&1; then
    echo "rocqchk succeeded on a corrupted file with: $args"
    cat "$D/out.log"
    exit 1
  fi
  if ! grep -q "Corrupted file" "$D/out.log"; then
    echo "unexpected rocqchk failure with: $args"
    cat "$D/out.log"
    exit 1
  fi
done

# -admit is still the way to ask for a library to be taken on faith.
"$BIN"rocqchk -R "$D" NorecOrder -norec NorecOrder.B -norec NorecOrder.A -admit NorecOrder.B
