#!/bin/sh
set -eu

runs="${1:-3}"
lake build LynxTest.Bench >/dev/null
run=1
while [ "$run" -le "$runs" ]; do
  for suite in Sum Reverse; do
    lake env lean "LynxTest/Integration/$suite.lean"
    lake env lean "Benchmarks/Native/$suite.lean"
  done
  run=$((run + 1))
done
