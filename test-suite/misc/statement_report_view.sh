#!/usr/bin/env bash

# An implementation-only unguarded fixpoint is needed to derive [boom], though
# the public module interface has an independent safe opaque [f]. The report
# must stay in the implementation view while it follows [boom] and [step].
set -eu

D=misc/statement_report_view
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
cp "$D/View.v" "$D/Prims.v" "$d/"

$coqc -Q "$d" StmtView "$d/View.v"
$coqc -allow-rewrite-rules -Q "$d" StmtView "$d/Prims.v"
printf 'public_f StmtView.View.Impl.f -\nboom StmtView.View.Impl.boom -\npublic_f_after StmtView.View.Impl.f -\nalias StmtView.View.alias_model -\nalias_module StmtView.View.alias_module_model -\nalias_impl StmtView.View.alias_impl_model -\nfun_alias StmtView.View.fun_alias_model -\nfallback StmtView.View.FallbackX.model -\nint StmtView.Prims.i -\n' > "$d/requests"
"$BIN"rocqchk -silent -statement-report "$d/requests" -Q "$d" StmtView StmtView.View StmtView.Prims > "$d/out" 2>&1
sed -n '/^STATEMENT REPORT$/,/^END STATEMENT REPORT$/p' "$d/out"
grep -q '^flag boom unsafe-fixpoint StmtView.View.Impl.f$' "$d/out"
grep -q '^axiom alias StmtView.View.A.ax$' "$d/out"
grep -q '^axiom alias_module StmtView.View.A.ax$' "$d/out"
grep -q '^axiom alias_impl StmtView.View.A.ax$' "$d/out"
grep -q '^axiom fun_alias StmtView.View.A.ax$' "$d/out"
if grep -q '^axiom alias StmtView.View.B.p$' "$d/out" ||
   grep -q '^axiom alias_module StmtView.View.C.p$' "$d/out" ||
   grep -q '^axiom alias_impl StmtView.View.C.ax$' "$d/out" ||
   grep -q '^axiom fun_alias StmtView.View.D.ax$' "$d/out"; then
  exit 1
fi
grep -q '^axiom int Corelib.Numbers.Cyclic.Int63.PrimInt63.int$' "$d/out"
grep -q '^axiom int StmtView.Prims.T$' "$d/out"
awk '$1 == "statement" && $2 == "public_f" { found_public_f = 1; public_f_ok = ($6 == 0 && $7 == 0) }
     $1 == "statement" && $2 == "boom" { found_boom = 1; boom_ok = ($6 == 0 && $7 == 2) }
     $1 == "statement" && $2 == "public_f_after" { found_public_f_after = 1; public_f_after_ok = ($6 == 0 && $7 == 0) }
     $1 == "statement" && $2 == "alias" { found_alias = 1; alias_ok = ($6 == 1 && $7 == 0) }
     $1 == "statement" && $2 == "alias_module" { found_alias_module = 1; alias_module_ok = ($6 == 1 && $7 == 0) }
     $1 == "statement" && $2 == "alias_impl" { found_alias_impl = 1; alias_impl_ok = ($6 == 1 && $7 == 0) }
     $1 == "statement" && $2 == "fun_alias" { found_fun_alias = 1; fun_alias_ok = ($6 == 1 && $7 == 0) }
     $1 == "statement" && $2 == "int" { found_int = 1; int_ok = ($6 == 2 && $7 == 0) }
     $1 == "statement" && $2 == "fallback" { found_fallback = 1; fallback_ok = ($6 == 0 && $7 == 0) }
     END { exit !(found_public_f && public_f_ok && found_boom && boom_ok && found_public_f_after && public_f_after_ok && found_alias && alias_ok && found_alias_module && alias_module_ok && found_alias_impl && alias_impl_ok && found_fun_alias && fun_alias_ok && found_fallback && fallback_ok && found_int && int_ok) }' "$d/out"

# A tab or carriage return is refused before a library is loaded, including in
# a comment line.
for bad in '# a\tcomment' '# a comment\r'; do
  printf "$bad\n" > "$d/bad"
  if "$BIN"rocqchk -silent -statement-report "$d/bad" -Q "$d" StmtView StmtView.View > "$d/bad.out" 2>&1; then
    exit 1
  fi
  grep -q -- '-statement-report: line 1 of' "$d/bad.out"
done
