#!/bin/sh

> test.expect
> test.log
exec >test.log 2>&1
expect () { echo '=== TEST ==='; ( echo "$@"; echo '=== TEST ===' ) >> test.expect; }
expect_ () { cat >> test.expect; echo '=== TEST ==='; echo '=== TEST ===' >> test.expect; }

ignore_linker_warnings () {
  # 32-bit debian and some osx versions issue spurious linker warnings
  # see https://github.com/ocaml/opam-repository/issues/3000 and 9728
  grep -v 'ld:.* warning:'
}

clean () {
  rm -f *.o *.cm*
}

clean
malfunction compile helloworld.mlf 2>&1 | ignore_linker_warnings
./helloworld
expect 'Hello, world!'

clean
malfunction compile -o foo helloworld.mlf 2>&1 | ignore_linker_warnings
./foo
expect 'Hello, world!'

clean
malfunction cmx helloworld.mlf
ocamlopt helloworld.cmx -o exec 2>&1 | ignore_linker_warnings
./exec
expect 'Hello, world!'

clean
malfunction cmo helloworld.mlf
ocamlc helloworld.cmo -o exec.byte
./exec
expect 'Hello, world!'

clean
ocamlc -opaque -c module.mli
malfunction cmx module.mlf
ocamlopt module.cmx main.ml -o main 2>&1 | ignore_linker_warnings
./main
expect_ <<EOF
42
10
true false
111
EOF

clean
ocamlc -opaque -c module.mli
malfunction cmo module.mlf
ocamlc module.cmo main.ml -o main.byte
./main.byte
expect_ <<EOF
42
10
true false
111
EOF
