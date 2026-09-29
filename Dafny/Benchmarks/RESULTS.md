# Daxie sum verification results

Captured 2026-09-29 on macOS 15.7.7, arm64, with Dafny nightly
`4.11.1+5f717bf447b19d38cad1b69b1bf9a9f102feccfb` and native `fp64` terms.
One verification core, five measured runs after one discarded warm-up per suite:

```console
sh Dafny/Benchmarks/run.sh 5
```

| Proof | Median verification time | Median solver resources |
| --- | ---: | ---: |
| Term sum contract | 106.822 ms | 96,191 |
| Term sum append | 164.322 ms | 673,532 |
| Native sum append | 41.494 ms | 17,473 |

The Term append proof took **3.96×** the native append proof's median time.
The native result type is already `int`, so it has no separate return-contract
proof. These are proof times over arbitrary lists, not sum execution times.

| Run | Term contract (ms) | Term append (ms) | Native append (ms) |
| --- | ---: | ---: | ---: |
| 1 | 108.090 | 164.062 | 41.494 |
| 2 | 104.511 | 164.322 | 40.721 |
| 3 | 107.468 | 164.604 | 42.318 |
| 4 | 106.822 | 166.428 | 41.564 |
| 5 | 106.288 | 162.884 | 41.489 |

Durations sum Dafny's correctness and contract well-formedness verification
batches for each final lemma. Supporting lemmas and imports are excluded.
The complete project passed first: **26 verified, 0 errors**. Each suite then
ran from source in a fresh process, with alternating suite order and unchanged
solver settings. Integer sum proofs use the verified, opaque addition contract.

At capture time, a clean C# generation and .NET 8.0.131 build also passed
semantic checks and sampled differential checks. The separate C# test harness
has since been replaced by explicit numeric edge cases in `Tests/Semantics.dfy`.
Non-finite result rejection has a verified lemma.

Raw CSV batches, verifier output, resource counts, and TSV summaries are
retained locally under `.benchmarks/20260929-114940-SiWiYq/` (ignored).
Every benchmark invocation creates a fresh log directory; the test runner
removes `.build/` before regenerating source and assemblies.
See [PROJECT.md](../PROJECT.md) for the model and measurement boundaries.
Dafny SMT batch timings are not directly comparable to Lean theorem-elaboration times.
