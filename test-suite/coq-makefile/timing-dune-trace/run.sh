#!/usr/bin/env bash

set -ex

. ../template/path-init.sh

../../../tools/make-one-time-file.py --json trace.jsonl > result.out

diff -u result.expected result.out
