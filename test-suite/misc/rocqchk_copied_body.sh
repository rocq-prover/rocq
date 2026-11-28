#!/usr/bin/env bash

# rocqchk checks an alias of an axiom, an opaque proof, a primitive operator
# or a symbol as a definition of its target, so it must refuse a copy whose
# body is not its target. In each case forge.ml gives the copy that an
# Include makes of one constant the body of the copy of another constant of
# the same type, and rocqchk must refuse the forged library:
# - axiom: H.a1, an alias of F.a1, gets the body F.a2.
# - opaque: H.o1, an alias of F.o1, gets the body F.o2.
# - primitive: H.add, an alias of F.add, gets the body F.sub.
# - symbol: H.s1, an alias of F.s1, gets the body F.s2.
# See coqchk/alias_primitive.v and coqchk/alias_symbol.v for the honest copies.

set -e

. misc/rocqchk-delta-alias/forge-lib.sh
ROOT=CopiedBody
C=$D/copied-body
LOG=$C/out.log

rm -rf "$C/forged"
rm -f "$C"/*.vo "$C"/*.vok "$C"/*.vos "$C"/*.glob
mkdir "$C/forged"
$coqc -noinit -R "$C" "$ROOT" "$C/Ax.v"
$coqc -R "$C" "$ROOT" "$C/Op.v"
$coqc -noinit -R "$C" "$ROOT" "$C/Prim.v"
$coqc -noinit -allow-rewrite-rules -R "$C" "$ROOT" "$C/Sym.v"
accept honest "$C" Ax Op Prim Sym
forge copy-body "$C/Ax.vo" "$C/forged/Ax.vo" H a2 a1
forge copy-body "$C/Op.vo" "$C/forged/Op.vo" H o2 o1
forge copy-body "$C/Prim.vo" "$C/forged/Prim.vo" H sub add
forge copy-body "$C/Sym.vo" "$C/forged/Sym.vo" H s2 s1
refuse axiom "Module typing error" "$C/forged" Ax
refuse opaque "Module typing error" "$C/forged" Op
refuse primitive "Module typing error" "$C/forged" Prim
refuse symbol "Module typing error" "$C/forged" Sym
exit $fail
