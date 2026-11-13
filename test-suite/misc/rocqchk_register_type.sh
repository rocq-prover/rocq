#!/usr/bin/env bash

# rocqchk must refuse a library that registers as a primitive type a
# constant that coqc does not register. The typing of a primitive literal
# uses the registered constant: with int : Set := Empty_set registered as
# the int63 type, Int 0 has the type int, and a match on it proves False.
# In each case of register-type/, forge.ml registers another constant as
# the int63 type, and gives z (zero in donor) the body Int 0:
# - donor: the definition int.
# - sealed: M.int, a parameter in the type of M, which M defines.
# - functor: R.M.int, where R := F N. Only the type of R declares it, as a
#   parameter, and N defines int.
# - dual: the parameter int, with the canonical name of the definition N.int.
# - other: int of the earlier library Base.
# - twice: MI.int of honest/Lib.v, which registers it already.
# The libraries that coqc compiles, among them honest/Lib.v, must be
# accepted.

set -e

. misc/rocqchk-delta-alias/forge-lib.sh
ROOT=RegisterType
R=$D/register-type
LOG=$R/out.log

not_a_parameter="is registered as the primitive type int63_type, but it is not a parameter"

C=$R/donor
compile "$C" Lib
accept donor "$C" Lib
forge int0 "$C/Lib.vo" "$C/forged/Lib.vo" zero
forge register "$C/forged/Lib.vo" "$C/forged/Lib.vo" RegisterType.Lib.int
refuse donor "$not_a_parameter" "$C/forged" Lib

# client_case <case> <error> <name> [<canonical>]: the forged Lib.vo of
# <case> registers <name>, with the canonical name <canonical> if it is
# given, and its forged Client.vo gives z the body Int 0.
client_case() {
  local name=$1 c=$R/$1 error=$2
  shift 2
  compile "$c" Lib Client
  accept $name "$c" Client
  forge register "$c/Lib.vo" "$c/forged/Lib.vo" "$@"
  forge int0 "$c/Client.vo" "$c/forged/Client.vo" z
  forge client "$c/forged/Client.vo" "$c/forged/Lib.vo" RegisterType.Lib "$c/forged/Client.vo"
  refuse $name "$error" "$c/forged" Client
}

client_case sealed "$not_a_parameter" RegisterType.Lib.M.int
client_case functor \
  "Retroknowledge registration for unknown constant RegisterType\.Lib\.R\.M\.int" \
  RegisterType.Lib.R.M.int
client_case dual \
  "is registered as the primitive type int63_type, but the registration gives it another canonical name, RegisterType\.Lib\.N\.int" \
  RegisterType.Lib.int RegisterType.Lib.N.int

C=$R/other
compile "$C" Base Lib
accept other "$C" Lib
cp "$C/Base.vo" "$C/forged/"
forge register "$C/Lib.vo" "$C/forged/Lib.vo" RegisterType.Base.int
refuse other \
  "is registered as the primitive type int63_type, but an earlier library declares it" \
  "$C/forged" Lib

# The forged library of case twice is made from the honest one.
C=$R/honest
compile "$C" Lib
accept honest "$C" Lib
forge register "$C/Lib.vo" "$C/forged/Lib.vo" RegisterType.Lib.MI.int
refuse twice "is registered twice as a primitive type" "$C/forged" Lib

exit $fail
