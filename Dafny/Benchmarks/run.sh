#!/bin/sh
set -eu
daxie_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
. "$daxie_root/tools.sh"
cd "$daxie_root"
runs=${1:-5}
case "$runs" in ''|*[!0-9]*|0) echo 'runs must be a positive integer' >&2; exit 1;; esac
[ "$runs" -gt 0 ] || { echo 'runs must be positive' >&2; exit 1; }
mkdir -p .benchmarks
output=$(mktemp -d "$daxie_root/.benchmarks/$(date +%Y%m%d-%H%M%S)-XXXXXX")
"$DAFNY" --version > "$output/environment.txt"
uname -sm >> "$output/environment.txt"
cat "$output/environment.txt"
"$DAFNY" verify dfyconfig.toml
printf 'run\tname\tms\tresources\n' > "$output/samples.tsv"
run=0
while [ "$run" -le "$runs" ]; do
  if [ $((run % 2)) -eq 0 ]; then suites='term native'; else suites='native term'; fi
  for suite in $suites; do
    if [ "$suite" = term ]; then
      source=Benchmarks/TermSum.dfy
      symbol=TermBenchmarks
    else
      source=Benchmarks/NativeSum.dfy
      symbol=NativeSum.SumAppend.
    fi
    log="$output/$run-$suite.csv"
    if ! "$DAFNY" verify "$source" --cores 1 --verification-time-limit 30 \
      --filter-symbol "$symbol" --log-format "csv;LogFileName=$log" \
      > "$output/$run-$suite.txt" 2>&1; then
      cat "$output/$run-$suite.txt" >&2
      exit 1
    fi
    awk -F, -v run="$run" -v suite="$suite" '
      NR == 1 { next }
      {
        name = $1; sub(/ \(.*/, "", name)
        if (suite == "term")
          expected = (name == "TermBenchmarks.SumContract" || name == "TermBenchmarks.SumAppend")
        else expected = name == "NativeSum.SumAppend"
        if (!expected || $2 != "Passed") { bad = 1; next }
        split($3, t, ":")
        ms[name] += (t[1] * 3600 + t[2] * 60 + t[3]) * 1000
        resources[name] += $4
      }
      END {
        for (name in ms) count++
        if (bad || count != (suite == "term" ? 2 : 1)) exit 1
        for (name in ms) printf "%d\t%s\t%.4f\t%d\n", run, name, ms[name], resources[name]
      }
    ' "$log" > "$output/$run-$suite.tsv"
    cat "$output/$run-$suite.tsv"
    if [ "$run" -ne 0 ]; then cat "$output/$run-$suite.tsv" >> "$output/samples.tsv"; fi
  done
  run=$((run + 1))
done
awk -F '\t' '
  NR == 1 { next }
  { n[$2]++; times[$2, n[$2]] = $3; resources[$2, n[$2]] = $4 }
  function median(values, name, count, i, j, value) {
    for (i = 2; i <= count; i++) {
      value = values[name, i]; j = i - 1
      while (j >= 1 && values[name, j] > value) {
        values[name, j + 1] = values[name, j]; j--
      }
      values[name, j + 1] = value
    }
    if (count % 2) return values[name, (count + 1) / 2]
    return (values[name, count / 2] + values[name, count / 2 + 1]) / 2
  }
  END {
    print "Proof\tMedian ms\tMedian resources"
    for (name in n) {
      m[name] = median(times, name, n[name])
      printf "%s\t%.3f\t%.0f\n", name, m[name], median(resources, name, n[name])
    }
    printf "Term/native append ratio: %.2fx\n", m["TermBenchmarks.SumAppend"] / m["NativeSum.SumAppend"]
  }
' "$output/samples.tsv" > "$output/summary.tsv"
cat "$output/summary.tsv"
printf 'Raw logs: %s\n' "$output"
