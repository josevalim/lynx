# Foxy verification results

The [Term-closure precondition experiment](../../Comparison/HigherOrderSum/REPORT.md)
reruns sum with `is_proper_list(xs, fn x -> is_integer(x) end)`: whole-CLI
client medians are **0.221s structural → 0.497s closure-based**, including both
supporting lemmas and both sum inductions.

The [2026-09-30 whole-CLI comparison](../../Comparison/WholeCli/REPORT.md) includes
startup, imports, all client set helpers, matched native map representations,
and a shared feature suite. Use that report for cross-project workflow
comparisons; the declaration timings below exclude that work.

Captured 2026-09-29 on arm64 macOS, F* 2026.03.24
(`70671ffb81fa30aba09b9d6e2af275dfbccaa8f8`), OCaml 5.4.1, Z3 4.16.0.
Five measured runs after one discarded warm-up per suite:

```console
sh FStar/Benchmarks/run.sh 5
```

| Proof | Term median | Native median | Term/native |
| --- | ---: | ---: | ---: |
| Sum result contract | 38 ms | Guaranteed by return type | — |
| Sum append | 56 ms | 15 ms | 3.73× |
| Set union contract | 50 ms | 56 ms | 0.89× |
| Set union commutativity | 101 ms | 19 ms | 5.32× |
| Set union empty identity | 15 ms | 14 ms | 1.07× |

Native sum uses `list int`; Term sum uses the dynamic `term` and `result`
types. Native sets use `FStar.FiniteMap.Base.map int (list int)`; Term sets use
association-list maps. Both set representations allow nonempty list values,
so preservation of the set invariant is a substantive property.

## Samples

All durations are milliseconds.

| Run | Term sum contract | Term append | Native append | Term set contract | Native set contract | Term commutative | Native commutative | Term empty | Native empty |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 38 | 55 | 15 | 52 | 56 | 100 | 18 | 16 | 15 |
| 2 | 38 | 56 | 15 | 50 | 56 | 100 | 19 | 15 | 14 |
| 3 | 37 | 55 | 16 | 52 | 56 | 101 | 19 | 15 | 13 |
| 4 | 38 | 56 | 15 | 50 | 55 | 101 | 19 | 16 | 14 |
| 5 | 37 | 56 | 16 | 50 | 56 | 104 | 20 | 15 | 13 |

## Boundaries and validation

The measured section is F*'s `FStarC.TypeChecker.Tc.process_one_decl` for each
named final proof. It includes declaration elaboration and verification, at
millisecond resolution. Imports, process startup, and supporting declarations
are excluded. Both Term sum proofs now perform their induction inside the
measured declaration. The former exact-sum theorem and arithmetic append
helper were removed. Only append domain preservation/success remains imported,
matching Lean/Daxie's sum support boundary. The append property explicitly
requires successful integer sums and successful append in its postcondition.
Native append also performs its induction in the measured lemma.

Map lookup/set-equality helpers remain outside timing, matching the supporting
work used by the other projects. Lean additionally proves domain coverage and
reasons through its environment-aware runtime; Daxie/Foxy use pure Result
equations here. The benchmarks share the integer-result, sum-append and set
properties, but their full contract machinery and timing metrics differ.

Each suite is forced to verify from source in a fresh F* process; supporting
imports use verified caches. Suite order alternates. The runner checks that
all nine expected measurements appear exactly once per repetition and retains
SMT query statistics in the raw logs. These are verification times, not
execution speeds. They cannot be directly compared with Daxie's SMT-batch
timings or treated as a language-performance ranking.

All **16 project modules verified** before measurement. Only the Foxy benchmark
runner and its verification gate ran for this correction; executable tests,
failure experiments, Lean and Daxie were not rerun. These measurements supersede
the previous Foxy sum timings, which excluded the main mathematical proof work.

Raw verifier logs, SMT query statistics, toolchain versions, samples, and
summaries are retained locally in ignored
`.benchmarks/20260929-183113-DdIa6j/`.
See [PROJECT.md](../PROJECT.md) for representation choices and proof limits.
