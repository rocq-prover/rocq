#!/usr/bin/env bash

# rocqchk must refuse a constant whose body is a primitive operator and
# whose type is not the operator's. Conversion and the VM compute with the
# operator whatever type the constant declares, so bogus : False with the
# body #int63_head0 is a closed proof of False. In each case of
# primitive-operator/, forge.ml gives the axiom bogus : False the body
# #int63_head0, whose type is int -> int:
# - registered: the library registers int, and declares operators as coqc
#   does.
# - unregistered: the library registers no primitive type, while coqc
#   declares head0 only once int is registered.
# The libraries that coqc compiles must be accepted.

set -e

. misc/rocqchk-delta-alias/forge-lib.sh
ROOT=PrimitiveOperator
P=$D/primitive-operator
LOG=$P/out.log

# check <case> <error>: rocqchk must accept the library of case <case>, and
# refuse its forged copy with an error that the extended regular expression
# <error> matches.
check() {
  local c=$P/$1
  compile "$c" Lib
  accept $1 "$c" Lib
  forge head0 "$c/Lib.vo" "$c/forged/Lib.vo" bogus
  refuse $1 "$2" "$c/forged" Lib
}

check registered "is the primitive operator head0, but its type is not the operator's"
check unregistered "The type int must be registered before this construction can be typechecked"

exit $fail
