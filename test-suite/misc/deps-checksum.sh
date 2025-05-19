#!/bin/sh
rm -f misc/deps/A/*.vo misc/deps/B/*.vo
$coqc -R misc/deps/A A misc/deps/A/A.v
$coqc -R misc/deps/B A misc/deps/B/A.v
$coqc -R misc/deps/B A misc/deps/B/B.v
mv misc/deps/A/A.vo misc/deps/B/A.vo
$coqc -R misc/deps/B A misc/deps/checksum.v
