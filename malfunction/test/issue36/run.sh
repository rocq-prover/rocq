#!/bin/sh
ocamlopt -c test_bytestring.mli
malfunction cmx test_bytestring.mlf
ocamlopt -c main.ml
ocamlopt -o main test_bytestring.cmx main.cmx
./main
