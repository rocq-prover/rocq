#!/usr/bin/env bash
# Check that both coqdep and coqtop/coqc support -R
# Check that both coqdep and coqtop/coqc takes -R preferably to installed $ROCQPATH
# See also bugs #2242, #2337, #2339

set -ex

export PATH=$BIN:$PATH

cd misc/deps/DistinctRoot
rm -rf _test
mkdir _test
find . -maxdepth 1 -not -name . -not -name _test -exec cp -r '{}' -t _test ';'
cd _test

if ! rocq dep -worker @ROCQWORKER@ -R A A -R B B A/File1.v A/File11.v B/File1.v File2.v > coqdep1.real 2>&1; then
  cat coqdep1.real
  exit 1
fi
diff -u --strip-trailing-cr coqdep1.out coqdep1.real || true

touch A/File1.vo # bad vo, must not be loaded
rocq c -R A A -R B B A/File11.v
rocq c -R A A -R B B B/File1.v

# now test with A "installed"
mkdir install
cp -r A install/A
export ROCQPATH=install
if ! rocq dep -worker @ROCQWORKER@ -R B B B/File1.v File2.v > coqdep2.real 2>&1; then
  cat coqdep2.real
  exit 1
fi
diff -u --strip-trailing-cr coqdep2.out coqdep2.real
rocq c -R B B File2.v

rm A/File1.vo
if ! rocq dep -worker @ROCQWORKER@ -R A A -R B B A/File1.v A/File11.v B/File1.v File2.v > coqdep3.real 2>&1; then
  cat coqdep3.real
  exit 1
fi
# reuse coqdep1.out: output should be same as first rocq dep run
diff -u --strip-trailing-cr coqdep1.out coqdep3.real
rocq c -R A A -R B B File2.v
