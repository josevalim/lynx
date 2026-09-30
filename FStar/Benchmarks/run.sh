#!/bin/sh
set -eu
foxy_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$foxy_root"
. ./tools.sh
runs=${1:-5}
case "$runs" in ''|*[!0-9]*|0) echo 'runs must be a positive integer' >&2; exit 1;; esac
[ "$runs" -gt 0 ] || exit 1
mkdir -p .benchmarks
output=$(mktemp -d "$foxy_root/.benchmarks/$(date +%Y%m%d-%H%M%S)-XXXXXX")
"$FSTAR" --version > "$output/environment.txt"
"$Z3" --version >> "$output/environment.txt"
ocamlopt -version >> "$output/environment.txt"
uname -sm >> "$output/environment.txt"
cat "$output/environment.txt"
sh verify.sh > "$output/verification.txt" 2>&1 || { cat "$output/verification.txt"; exit 1; }
printf 'run\tname\tms\n' > "$output/samples.tsv"
printf 'run\tsuite\tseconds\n' > "$output/cli-samples.tsv"
run=0
while [ "$run" -le "$runs" ]; do
  if [ $((run % 2)) -eq 0 ]; then suites='TermSum NativeSum TermSets NativeSets'; else suites='NativeSets TermSets NativeSum TermSum'; fi
  for suite in $suites; do
    case "$suite" in
      TermSum) names='sum_contract sum_append'; count=2 ;;
      NativeSum) names='sum_append'; count=1 ;;
      *) names='union_contract union_commutative union_empty'; count=3 ;;
    esac
    log="$output/$run-$suite.txt"
    # Force the suite itself to be checked; support imports may use verified caches.
    if ! FOXY_TIME_OUTPUT="$output/$run-$suite.time" foxy_check --force --timing --query_stats "Benchmarks/Foxy.Bench.$suite.fst" > "$log" 2>&1; then cat "$log" >&2; exit 1; fi
    awk -v run="$run" -v suite="$suite" -v names="$names" -v expectedCount="$count" '
      BEGIN { split(names, list, " "); for (i in list) expected["Foxy.Bench." suite "." list[i]]=1 }
      /, profiled FStarC.TypeChecker.Tc.process_one_decl:/ {
        name=$1; sub(/,$/, "", name)
        if (name in expected) { seen[name]++; ms[name]=$(NF-1) }
      }
      END {
        for (name in expected) { if (seen[name] != 1) exit 1; count++ }
        if (count != expectedCount) exit 1
        for (name in expected) printf "%d\t%s\t%d\n", run, name, ms[name]
      }
    ' "$log" > "$output/$run-$suite.tsv"
    cat "$output/$run-$suite.tsv"
    if [ "$run" -ne 0 ]; then
      cat "$output/$run-$suite.tsv" >> "$output/samples.tsv"
      awk -v run="$run" -v suite="$suite" '$1 == "real" { printf "%d\t%s\t%.2f\n", run, suite, $2 }' \
        "$output/$run-$suite.time" >> "$output/cli-samples.tsv"
    fi
  done
  run=$((run+1))
done
awk -F '\t' '
  NR==1 { next }
  { n[$2]++; values[$2,n[$2]]=$3 }
  END {
    print "Proof\tMedian ms"
    for (name in n) {
      count=n[name]
      for (i=2;i<=count;i++) {
        v=values[name,i];j=i-1
        while (j>=1 && values[name,j]>v) { values[name,j+1]=values[name,j];j-- }
        values[name,j+1]=v
      }
      m=(count%2) ? values[name,(count+1)/2] : (values[name,count/2]+values[name,count/2+1])/2
      printf "%s\t%.1f\n", name,m
    }
  }
' "$output/samples.tsv" > "$output/summary.tsv"
cat "$output/summary.tsv"
awk -F '\t' '
  NR==1 { next }
  { n[$2]++; values[$2,n[$2]]=$3 }
  END {
    print "Suite\tMedian whole-CLI seconds"
    for (name in n) {
      count=n[name]
      for (i=2;i<=count;i++) {
        v=values[name,i];j=i-1
        while (j>=1 && values[name,j]>v) { values[name,j+1]=values[name,j];j-- }
        values[name,j+1]=v
      }
      m=(count%2) ? values[name,(count+1)/2] : (values[name,count/2]+values[name,count/2+1])/2
      printf "%s\t%.2f\n", name,m
    }
  }
' "$output/cli-samples.tsv" > "$output/cli-summary.tsv"
cat "$output/cli-summary.tsv"
printf 'Raw logs: %s\n' "$output"
