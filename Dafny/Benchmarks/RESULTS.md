# Daxie sum and set verification results

Sum now uses typed pure/effectful table entries and the same specialized
Term-callback precondition as the retained Lean run. F* results are in
[its results](../../FStar/Benchmarks/RESULTS.md); the cross-project comparison
and whole-CLI measurements are below.

Captured 2026-09-30 on macOS 15.7.7, arm64, with Dafny nightly
`4.11.1+5f717bf447b19d38cad1b69b1bf9a9f102feccfb` and native `fp64` terms.
One verification core, five measured runs after one discarded warm-up per suite:

```console
sh Dafny/Benchmarks/run.sh 5
```

| Proof | Median verification time | Median solver resources |
| --- | ---: | ---: |
| Term sum contract | 219.499 ms | 338,984 |
| Term sum append | 327.658 ms | 877,587 |
| Native sum append | 38.340 ms | 17,473 |
| Term set union contract | 345.831 ms | 330,966 |
| Native set union contract | 39.415 ms | 28,264 |
| Term set union commutativity | 375.630 ms | 361,244 |
| Native set union commutativity | 17.642 ms | 81,686 |
| Term set union empty identity | 389.052 ms | 360,755 |
| Native set union empty identity | 17.360 ms | 28,826 |

The Term append proof took **8.55×** the native append proof's median time.
The native result type is already `int`, so it has no separate return-contract
proof. These are proof times over arbitrary inputs, not execution times.
The set proofs reproduce Lean's preservation, commutativity, and empty-map
properties. Term maps use association lists with exact keys and first-binding
precedence; native maps use `map<int, List<int>>`. Set expectations are logical
predicates on effective bindings, excluding shadowed entries.

| Run | Term contract (ms) | Term append (ms) | Native append (ms) |
| --- | ---: | ---: | ---: |
| 1 | 222.211 | 330.677 | 38.619 |
| 2 | 219.499 | 327.658 | 38.026 |
| 3 | 220.810 | 332.687 | 38.340 |
| 4 | 217.664 | 322.933 | 38.994 |
| 5 | 211.805 | 324.941 | 38.124 |

Compared with a separate source copy of preceding commit `35b52a8`, built
and measured on this machine with the same tools and five runs after warm-up:

| Existing proof | Before | After | Change |
| --- | ---: | ---: | ---: |
| Term sum contract | 149.701 ms | 219.499 ms | +46.6% |
| Term sum append | 238.768 ms | 327.658 ms | +37.2% |
| Native sum append | 41.060 ms | 38.340 ms | -6.6% |

The previous Sum expectation was structural. These changes include typed table
entries, arithmetic purity contracts, and callback-based expectations; they do
not isolate one source of overhead. A verified callback summary reduces
repeated lookup expansion without moving sum induction outside timing.

Durations sum Dafny's correctness and contract well-formedness verification
batches for each final lemma. Supporting lemmas and imports are excluded.
The complete project passed first: **94 verified, 0 errors**. Each suite then
ran from source in a fresh process, with alternating suite order and unchanged
solver settings. Integer sum proofs use the verified, opaque addition contract.

A clean C# generation and .NET 8.0.131 build also passed all
Dafny semantic tests, including numeric edge cases, closures, process effects,
and association-list maps. Non-finite result rejection has a verified lemma.
The retained Lean run passed `lake test`; Lean was not rerun on this branch.

## Cross-project comparison

All three Sum examples traverse Term cons cells, invoke an integer predicate
closure through `pureApply`, and distinguish typed pure bodies from effectful
requests. Their specialized traversal is proved equivalent to the generic
callback traversal. Integer-result and append proofs retain their induction
inside the measured declarations; append domain preservation and callback
summaries are supporting library work.

| Proof | Lean elaboration (ms) | Dafny SMT batches (ms) | F* declaration checking (ms) |
| --- | ---: | ---: | ---: |
| Sum result contract | 145.80 | 219.499 | 39 |
| Sum append | 626.15 | 327.658 | 67 |
| Native append | 12.63 | 38.340 | 15 |
| Term set union contract | 75.49 | 345.831 | 47 |
| Native set union contract | 13.59 | 39.415 | 51 |
| Term set union commutativity | 50.85 | 375.630 | 95 |
| Native set union commutativity | 161.13 | 17.642 | 19 |
| Term set union empty identity | 15.59 | 389.052 | 15 |
| Native set union empty identity | 6.31 | 17.360 | 13 |

Lean numbers are retained from the previous branch's five-run measurement on
this machine, not remeasured or inferred. The columns have different timing
boundaries: **they are not a speed ranking**. Lean additionally proves coverage
and uses environment-aware contracts; Dafny/F* use pure Result equations. The
full runtime feature sets also differ (for example, Lean supports receive and
process dictionaries); this experiment matches the Sum workload. Native set maps use different host
libraries, so those rows also compare library choices. Retained Lean-only
Reverse medians are 11.52 ms (contract), 8.86 ms (involution), and 75.54 ms
(append), with native involution/append at 0.72/5.01 ms. These projects have no
corresponding Reverse benchmark.

| Complete CLI invocation | Dafny median (s) | F* median (s) | Dafny/F* |
| --- | ---: | ---: | ---: |
| Term sum (both proofs) | 1.93 | 0.24 | 8.04× |
| Native sum | 0.73 | 0.15 | 4.87× |
| Term sets (three proofs) | 2.39 | 0.38 | 6.29× |
| Native sets (three proofs) | 0.79 | 0.28 | 2.82× |

CLI wall times include startup, parsing/import loading, final-proof checking,
and logging. Each suite runs in a fresh process; one warm-up is discarded,
five runs are measured, and suite order alternates. Projects are measured
sequentially. Supporting libraries are verified first: Dafny skips their proof
batches with its symbol filter; F* loads checked imports. This is a client
verification comparison, not a cold verification of every library definition.
Both use Z3 4.16.0, but their SMT encodings and verifier pipelines differ.
Wall times use `/usr/bin/time -p` with 0.01-second resolution. No Lean whole-CLI
measurement was retained, so that comparison is unavailable.

Current logs are ignored local files under
`.benchmarks/20260930-141934-NicZ8c/`; no benchmark evidence is added to git.
See [PROJECT.md](../PROJECT.md) for the model and measurement boundaries.
