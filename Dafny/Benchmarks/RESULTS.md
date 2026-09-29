# Daxie sum and set verification results

The [Term-closure precondition experiment](../../Comparison/HigherOrderSum/REPORT.md)
reruns sum with `is_proper_list(xs, fn x -> is_integer(x) end)`: corrected
whole-CLI client medians are **1.698s structural → 3.375s closure-based**,
including both supporting lemmas and both sum inductions.

The [2026-09-30 whole-CLI comparison](../../Comparison/WholeCli/REPORT.md) includes
startup, imports, supporting proofs, matched native map representations, and a
shared feature suite. Use that report for cross-project workflow comparisons;
the declaration timings below exclude that work.

Captured 2026-09-29 on macOS 15.7.7, arm64, with Dafny nightly
`4.11.1+5f717bf447b19d38cad1b69b1bf9a9f102feccfb` and native `fp64` terms.
One verification core, five measured runs after one discarded warm-up per suite:

```console
sh Dafny/Benchmarks/run.sh 5
```

| Proof | Median verification time | Median solver resources |
| --- | ---: | ---: |
| Term sum contract | 152.646 ms | 167,270 |
| Term sum append | 246.792 ms | 643,684 |
| Native sum append | 40.821 ms | 17,473 |
| Term set union contract | 388.210 ms | 330,966 |
| Native set union contract | 41.337 ms | 28,264 |
| Term set union commutativity | 368.437 ms | 361,244 |
| Native set union commutativity | 18.186 ms | 81,686 |
| Term set union empty identity | 385.469 ms | 360,755 |
| Native set union empty identity | 17.890 ms | 28,826 |

The Term append proof took **6.05×** the native append proof's median time.
The native result type is already `int`, so it has no separate return-contract
proof. These are proof times over arbitrary inputs, not execution times.
The set proofs reproduce Lean's preservation, commutativity, and empty-map
properties. Term maps use association lists with exact keys and first-binding
precedence; native maps use `map<int, List<int>>`. Set expectations are logical
predicates on effective bindings, excluding shadowed entries.

| Run | Term contract (ms) | Term append (ms) | Native append (ms) |
| --- | ---: | ---: | ---: |
| 1 | 159.124 | 246.792 | 40.597 |
| 2 | 152.646 | 241.651 | 43.577 |
| 3 | 151.949 | 247.294 | 41.137 |
| 4 | 153.293 | 263.263 | 40.821 |
| 5 | 149.110 | 241.137 | 40.541 |

Compared with a separate source copy of preceding commit `b05d89d`, measured
on this machine with the same toolchain and five runs after warm-up:

| Existing proof | Before | After | Change |
| --- | ---: | ---: | ---: |
| Term sum contract | 104.280 ms | 152.646 ms | +46.4% |
| Term sum append | 162.403 ms | 246.792 ms | +52.0% |
| Native sum append | 40.388 ms | 40.821 ms | +1.1% |

The expanded Term/Result model and use of `Bind` increase the Term proof times.
The append proof's solver resources fell from 673,532 to 643,684 despite the
longer time; contract resources increased from 96,191 to 167,270. These
measurements compare the complete change, not isolated causes of the slowdown.

Durations sum Dafny's correctness and contract well-formedness verification
batches for each final lemma. Supporting lemmas and imports are excluded.
The complete project passed first: **84 verified, 0 errors**. Each suite then
ran from source in a fresh process, with alternating suite order and unchanged
solver settings. Integer sum proofs use the verified, opaque addition contract.

At capture time, a clean C# generation and .NET 8.0.131 build also passed all
Dafny semantic tests, including numeric edge cases, closures, process effects,
and association-list maps. Non-finite result rejection has a verified lemma.
The existing Lean `lake test` suite also passed; no Lean sources changed.

Raw CSV batches, verifier output, resource counts, and TSV summaries are
retained locally under `.benchmarks/20260929-124307-yt1E4y/` (ignored).
Baseline logs are in
`/private/tmp/daxie-baseline-20260929/.benchmarks/20260929-122756-CI25vK/`.
Every benchmark invocation creates a fresh log directory; the test runner
removes `.build/` before regenerating source and assemblies.
See [PROJECT.md](../PROJECT.md) for the model and measurement boundaries.
Dafny SMT batch timings are not directly comparable to Lean theorem-elaboration times.
