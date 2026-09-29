#!/bin/sh
set -eu
foxy_root=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$foxy_root"
. ./tools.sh
mkdir -p .build/cache
for source in \
  Foxy/Foxy.Float.fst Foxy/Foxy.Term.fst Foxy/Foxy.Compare.fst \
  Foxy/Foxy.Arithmetic.fst Foxy/Foxy.Maps.fst Foxy/Foxy.Process.fst \
  Foxy/Foxy.Runner.fst Foxy/Foxy.Sum.fst Foxy/Foxy.ListPredicates.fst Foxy/Foxy.Sets.fst \
  Benchmarks/Foxy.Bench.TermSum.fst Benchmarks/Foxy.Bench.NativeSum.fst \
  Benchmarks/Foxy.Bench.TermSets.fst Benchmarks/Foxy.Bench.NativeSets.fst \
  Tests/Foxy.Tests.Program.fst Tests/Foxy.Tests.Proofs.fst Tests/Foxy.Tests.Main.fst
do
  foxy_check --force --cache_checked_modules "$source"
done
