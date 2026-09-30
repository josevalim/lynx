# Foxy verification results

Sum now uses typed pure/effectful entries and the same specialized Term-callback
precondition as Lean. The [cross-project comparison](../../Dafny/Benchmarks/RESULTS.md#cross-project-comparison)
preserves Lean's measurements and reports fresh Dafny/F* whole-CLI timings.

Captured 2026-09-30 on arm64 macOS, F* 2026.03.24
(`70671ffb81fa30aba09b9d6e2af275dfbccaa8f8`), OCaml 5.4.1, Z3 4.16.0.
Five measured runs after one discarded warm-up per suite:

```console
sh FStar/Benchmarks/run.sh 5
```

| Proof | Term median | Native median | Term/native |
| --- | ---: | ---: | ---: |
| Sum result contract | 39 ms | Guaranteed by return type | — |
| Sum append | 67 ms | 15 ms | 4.47× |
| Set union contract | 47 ms | 51 ms | 0.92× |
| Set union commutativity | 95 ms | 19 ms | 5.00× |
| Set union empty identity | 15 ms | 13 ms | 1.15× |

Native sum uses `list int`; Term sum uses the dynamic `term` and `result`
types. Native sets use `FStar.FiniteMap.Base.map int (list int)`; Term sets use
association-list maps. Both set representations allow nonempty list values,
so preservation of the set invariant is a substantive property.

## Samples

All durations are milliseconds.

| Run | Term sum contract | Term append | Native append | Term set contract | Native set contract | Term commutative | Native commutative | Term empty | Native empty |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 40 | 69 | 15 | 47 | 51 | 95 | 18 | 15 | 13 |
| 2 | 41 | 70 | 15 | 47 | 51 | 94 | 19 | 15 | 13 |
| 3 | 39 | 67 | 15 | 47 | 50 | 95 | 18 | 15 | 13 |
| 4 | 38 | 66 | 15 | 46 | 53 | 94 | 19 | 15 | 13 |
| 5 | 38 | 67 | 15 | 48 | 52 | 95 | 19 | 15 | 13 |

## Boundaries and validation

The measured section is F*'s `FStarC.TypeChecker.Tc.process_one_decl` for each
named final proof. It includes declaration elaboration and verification, at
millisecond resolution. Imports, process startup, and supporting declarations
are excluded. Whole-CLI wall times are recorded separately in the linked
comparison. Both Term sum proofs now perform their induction inside the
measured declaration. The former exact-sum theorem and arithmetic append
helper were removed. Callback specialization and a verified opaque per-element
callback summary are imported alongside append domain preservation/success,
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

All **17 project modules verified** before measurement. A clean extraction,
OCaml compilation, and semantic test run also passed, including direct captured
pure calls, pure errors, effectful fallback, and invalid callback lists. The
existing strict-positivity and function-equality probes were rejected as expected.
Dafny's full verification and executable suite also passed; Lean was not rerun.

Raw verifier logs, SMT query statistics, toolchain versions, samples, and
summaries are retained locally in ignored
`.benchmarks/20260930-142028-38yi2Z/`.
See [PROJECT.md](../PROJECT.md) for representation choices and proof limits.
