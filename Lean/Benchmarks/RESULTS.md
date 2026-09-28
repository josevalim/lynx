# Benchmark results

## Return discovery independent of opacity (2026-09-26)

Five interleaved runs each of commit `9edc041`, the opaque-only discovery snapshot,
and general discovery, built from their own sources on the same macOS arm64
machine with Lean 4.33.1. All 210 timed declarations passed. `lake test` passed
for both discovery implementations, including regressions and proof audits.
Medians exclude imports and supporting lemmas.

| Translated proof | Commit (ms) | Opaque-only (ms) | General (ms) | Change vs opaque-only |
| --- | ---: | ---: | ---: | ---: |
| Sum result contract | 116.42 | 124.97 | 124.53 | -0.4% |
| Sum append | 507.80 | 525.79 | 527.30 | +0.3% |
| Reverse return contract | 11.48 | 11.75 | 11.84 | +0.8% |
| Reverse involution | 8.80 | 8.93 | 8.86 | -0.8% |
| Reverse append | 77.24 | 75.03 | 75.88 | +1.1% |
| Sets union contract | 76.51 | 77.51 | 77.06 | -0.6% |
| Sets union commutativity | 49.61 | 49.96 | 50.64 | +1.4% |
| Sets union empty identity | 16.23 | 16.19 | 16.38 | +1.2% |

Return-shape candidates come from existing simp equations for reachable functions,
regardless of opacity. Only implementation traversal depends on `lynx_opaque`;
`Erlang.erlang.«+/2»` retains that annotation. Generated equations installed for unfolding are
excluded from hint discovery, and all summaries require independent proofs.
General discovery leaves translated proof medians within -0.8% to +1.4% of the
opaque-only version. Native control medians varied from -10.3% to +5.6%, with the
largest relative change in sub-millisecond reverse involution. These differences
do not establish a speedup. The combined changes remain 7.0% slower for the sum
contract and 3.8% slower for sum-append than the commit.

## Staged unfolding (2026-09-26)

Compared with `9edc041`, with each revision built from its own source on the same
macOS arm64 machine using Lean 4.33.1. Five runs per revision alternated execution
order. All 140 timed declarations passed; `lake test` passed on both revisions,
including the new staged-unfolding regressions and axiom audits on the new version.
Medians exclude imports and supporting lemmas.

| Translated proof | Before (ms) | After (ms) | Change |
| --- | ---: | ---: | ---: |
| Sum result contract | 114.13 | 122.89 | +7.7% |
| Sum append | 501.44 | 514.27 | +2.6% |
| Reverse return contract | 11.44 | 11.73 | +2.5% |
| Reverse involution | 9.37 | 9.44 | +0.7% |
| Reverse append | 77.62 | 77.05 | -0.7% |
| Sets union contract | 75.85 | 76.93 | +1.4% |
| Sets union commutativity | 49.90 | 51.43 | +3.1% |
| Sets union empty identity | 16.81 | 16.13 | -4.0% |

The general policy preserves all existing proofs with modest overhead; it does
not establish a suite-wide speedup. Native control medians varied from -6.7% to
+1.2%. Equation indexing is shared between the normal and fallback contexts.
Explicit `lynx_opaque` boundaries remain: removing `Erlang.erlang.«+/2»`'s boundary slowed
sum-append by about 32% in an isolated trial, so it was retained.

## Previous capture

Captured on 2026-09-10 with Lean 4.33.1 on macOS arm64.

```sh
sh Benchmarks/run.sh 5
```

All 30 fresh Lean processes and 70 timed declarations passed.
Times are median proof-elaboration milliseconds, not executable runtime.
Measurements exclude imports and supporting lemmas; later proofs in each file
may reuse earlier results and cached summaries.

| Target | Translated (ms) | Native (ms) |
| --- | ---: | ---: |
| Sum result contract | 150.01 | — |
| Sum append | 555.40 | 11.61 |
| Reverse return contract | 10.20 | — |
| Reverse involution | 6.54 | 0.70 |
| Reverse append | 78.85 | 4.55 |
| Sets union contract | 67.87 | 12.11 |
| Sets union commutativity | 47.45 | 142.34 |
| Sets union empty identity | 16.91 | 5.23 |

## Captured output

Each consecutive group of 14 lines is one run.

```text
LYNX_BENCH erlang/sum-contract 150.01ms
LYNX_BENCH erlang/sum-append 552.74ms
LYNX_BENCH native/sum-append 11.54ms
LYNX_BENCH erlang/reverse-contract 10.14ms
LYNX_BENCH erlang/reverse-involution 6.48ms
LYNX_BENCH erlang/reverse-append 78.45ms
LYNX_BENCH native/reverse-involution 0.82ms
LYNX_BENCH native/reverse-append 4.38ms
LYNX_BENCH erlang/sets-union-contract 68.64ms
LYNX_BENCH erlang/sets-union-commutative 47.54ms
LYNX_BENCH erlang/sets-union-empty 17.07ms
LYNX_BENCH native/sets-union-contract 12.07ms
LYNX_BENCH native/sets-union-commutative 143.27ms
LYNX_BENCH native/sets-union-empty 5.23ms
LYNX_BENCH erlang/sum-contract 150.94ms
LYNX_BENCH erlang/sum-append 557.07ms
LYNX_BENCH native/sum-append 11.62ms
LYNX_BENCH erlang/reverse-contract 10.12ms
LYNX_BENCH erlang/reverse-involution 6.59ms
LYNX_BENCH erlang/reverse-append 78.56ms
LYNX_BENCH native/reverse-involution 0.69ms
LYNX_BENCH native/reverse-append 4.46ms
LYNX_BENCH erlang/sets-union-contract 67.86ms
LYNX_BENCH erlang/sets-union-commutative 47.36ms
LYNX_BENCH erlang/sets-union-empty 16.87ms
LYNX_BENCH native/sets-union-contract 11.88ms
LYNX_BENCH native/sets-union-commutative 142.34ms
LYNX_BENCH native/sets-union-empty 5.21ms
LYNX_BENCH erlang/sum-contract 150.05ms
LYNX_BENCH erlang/sum-append 555.40ms
LYNX_BENCH native/sum-append 11.61ms
LYNX_BENCH erlang/reverse-contract 10.20ms
LYNX_BENCH erlang/reverse-involution 6.41ms
LYNX_BENCH erlang/reverse-append 79.49ms
LYNX_BENCH native/reverse-involution 0.70ms
LYNX_BENCH native/reverse-append 4.66ms
LYNX_BENCH erlang/sets-union-contract 67.87ms
LYNX_BENCH erlang/sets-union-commutative 47.45ms
LYNX_BENCH erlang/sets-union-empty 16.90ms
LYNX_BENCH native/sets-union-contract 12.38ms
LYNX_BENCH native/sets-union-commutative 142.18ms
LYNX_BENCH native/sets-union-empty 5.21ms
LYNX_BENCH erlang/sum-contract 149.73ms
LYNX_BENCH erlang/sum-append 554.00ms
LYNX_BENCH native/sum-append 11.61ms
LYNX_BENCH erlang/reverse-contract 10.43ms
LYNX_BENCH erlang/reverse-involution 6.72ms
LYNX_BENCH erlang/reverse-append 79.75ms
LYNX_BENCH native/reverse-involution 0.70ms
LYNX_BENCH native/reverse-append 4.59ms
LYNX_BENCH erlang/sets-union-contract 68.05ms
LYNX_BENCH erlang/sets-union-commutative 47.51ms
LYNX_BENCH erlang/sets-union-empty 16.93ms
LYNX_BENCH native/sets-union-contract 12.11ms
LYNX_BENCH native/sets-union-commutative 142.56ms
LYNX_BENCH native/sets-union-empty 5.24ms
LYNX_BENCH erlang/sum-contract 149.45ms
LYNX_BENCH erlang/sum-append 556.22ms
LYNX_BENCH native/sum-append 11.72ms
LYNX_BENCH erlang/reverse-contract 10.20ms
LYNX_BENCH erlang/reverse-involution 6.54ms
LYNX_BENCH erlang/reverse-append 78.85ms
LYNX_BENCH native/reverse-involution 0.70ms
LYNX_BENCH native/reverse-append 4.55ms
LYNX_BENCH erlang/sets-union-contract 67.72ms
LYNX_BENCH erlang/sets-union-commutative 47.42ms
LYNX_BENCH erlang/sets-union-empty 16.91ms
LYNX_BENCH native/sets-union-contract 12.33ms
LYNX_BENCH native/sets-union-commutative 142.33ms
LYNX_BENCH native/sets-union-empty 5.30ms
```
