#!/bin/sh

expect () { echo "$@" >> test.log; }
expect_ () { cat >> test.log; }

malfunction compile helloworld.mlf
./helloworld
expect 'Hello, world!'

malfunction compile -o foo helloworld.mlf
./foo
expect 'Hello, world!'

malfunction cmx helloworld.mlf
ocamlopt helloworld.cmx -o exec
./exec
expect 'Hello, world!'

ocamlc -opaque -c module.mli
malfunction cmx module.mlf
ocamlopt module.cmx main.ml -o main
./main
expect_ <<EOF
42
10
true false
111
EOF
