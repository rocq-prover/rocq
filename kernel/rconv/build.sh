#!/usr/bin/env bash
# Build the Rust conversion for the word size of the OCaml compiler.
set -e
if [ "$RCONV_WORD_SIZE" = 32 ]; then
  target=i686-unknown-linux-gnu
  cargo build --release --offline --quiet --target-dir target --target "$target"
  dir="target/$target/release"
else
  cargo build --release --offline --quiet --target-dir target
  dir=target/release
fi
cp "$dir/librconv_rs.a" librconv_rs.a
cp "$dir/librconv_rs.so" dllrconv_rs.so
