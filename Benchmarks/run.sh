#!/bin/sh
set -eu

runs="${1:-3}"
lake build Benchmarks.Common >/dev/null
run=1
while [ "$run" -le "$runs" ]; do
  for file in Erlang Native; do
    lake env lean "Benchmarks/Sum/$file.lean"
  done
  run=$((run + 1))
done
