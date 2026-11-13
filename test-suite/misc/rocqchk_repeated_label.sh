#!/usr/bin/env bash

# rocqchk must refuse a structure that gives one label to two fields in one
# of the two namespaces of coqc. One holds the constants, the rewrite rule
# blocks and the types and constructors of inductive blocks. The other holds
# the modules and module types. The environment keeps the last field with a
# label, so the second field replaces the first after the fields between
# them were checked against it. In each case of repeated-label/, forge.ml
# forges the library, and relinks the client to the forged library:
# - axiom: Axiom ax : False, proof : False := ax and twin : unit := tt,
#   with twin labelled ax. The client proves False with proof.
# - registered: int : Set := Empty_set, zero : int := Int 0 and
#   boom : False := match zero return False with end, with int registered
#   as the int63 type and a parameter int : Set inserted before it. The
#   registration is checked on the parameter, the definition replaces it,
#   and the client proves False with boom.
# - modtype: two module types T and U, with U labelled T.
# The files that coqc compiles must be accepted, and so must shared/Lib.v,
# whose labels repeat as coqc lets them.

set -e

. misc/rocqchk-delta-alias/forge-lib.sh
ROOT=RepeatedLabel
L=$D/repeated-label
LOG=$L/out.log

# relink <case>: the forged Client.vo of case <case>, with the forged Lib.vo
# as its dependency.
relink() {
  local c=$L/$1
  forge client "$c/Client.vo" "$c/forged/Lib.vo" RepeatedLabel.Lib "$c/forged/Client.vo"
}

objects="twice among its constants, inductive types, constructors and rewrite rules"

compile "$L/shared" Lib
accept shared "$L/shared" Lib

C=$L/axiom
compile "$C" Lib Client
accept axiom "$C" Lib Client
forge relabel "$C/Lib.vo" "$C/forged/Lib.vo" twin ax
relink axiom
refuse axiom "RepeatedLabel\.Lib declares the label ax $objects" "$C/forged" Lib Client

C=$L/registered
compile "$C" Lib Client
accept registered "$C" Lib Client
forge int0 "$C/Lib.vo" "$C/forged/Lib.vo" zero
forge register "$C/forged/Lib.vo" "$C/forged/Lib.vo" RepeatedLabel.Lib.int
forge repeat-parameter "$C/forged/Lib.vo" "$C/forged/Lib.vo" int
relink registered
refuse registered "RepeatedLabel\.Lib declares the label int $objects" "$C/forged" Lib Client

C=$L/modtype
compile "$C" Lib Client
accept modtype "$C" Lib Client
forge relabel "$C/Lib.vo" "$C/forged/Lib.vo" U T
relink modtype
refuse modtype \
  "RepeatedLabel\.Lib declares the label T twice among its modules and module types" \
  "$C/forged" Lib Client

exit $fail
