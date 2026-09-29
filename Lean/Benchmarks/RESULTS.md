# Benchmark results

For the 2026-09-30 cross-project rerun measuring **whole CLI wall time**, including
supporting proofs and matched association-list native controls, see the
[comparison report](../../Comparison/WholeCli/REPORT.md). The declaration times
below measure a different boundary.

Captured on 2026-09-29 with Lean 4.33.1 on macOS arm64.

```sh
sh Benchmarks/run.sh 5
```

All 30 fresh Lean processes and 70 timed declarations passed.
Times are median proof-elaboration milliseconds, not executable runtime.
Measurements exclude imports and supporting lemmas; later proofs in each file
may reuse earlier results and cached summaries.

| Target | Translated (ms) | Native (ms) |
| --- | ---: | ---: |
| Sum result contract | 123.36 | — |
| Sum append | 556.55 | 13.03 |
| Reverse return contract | 11.61 | — |
| Reverse involution | 9.00 | 0.73 |
| Reverse append | 75.60 | 5.24 |
| Sets union contract | 77.29 | 13.43 |
| Sets union commutativity | 52.41 | 165.67 |
| Sets union empty identity | 16.56 | 6.26 |

## Internal proof simplification check (2026-09-29)

Compared commit `a6b79bc` against the working tree with shorter proofs of
`Result.bind_ok`, `Result.bind_assoc_proof`, and the runner's `accProcess`.
These three private proof bodies shrink from 103 lines to six; their statements,
runtime definitions, public API, and registered simplification rules are unchanged.
The monad laws use induction followed by `simp_all only [Result.bind]`.
The termination proof shares constructor setup and retains an explicit
parallel-scheduling case. Purity wrappers and tactic search machinery remain.

The baseline was extracted from the commit into a separate directory and built
from its own source. Both revisions ran one discarded warm-up and five measured
repetitions on the same machine, sequentially without concurrent verifier jobs.
All 70 measured declarations passed for each revision; `lake test` also passed
for the changed version, including API and proof audits. Test-build timings are
excluded. [All Term/native samples](proof-simplification-samples.tsv).

| Translated proof | Baseline median (ms) | Simplified median (ms) |
| --- | ---: | ---: |
| Sum result contract | 126.65 | 128.22 |
| Sum append | 575.52 | 575.65 |
| Reverse return contract | 11.65 | 12.58 |
| Reverse involution | 9.47 | 9.47 |
| Reverse append | 77.92 | 77.61 |
| Sets union contract | 80.62 | 80.09 |
| Sets union commutativity | 53.59 | 52.63 |
| Sets union empty identity | 17.48 | 16.72 |

This supports keeping the shorter proofs for maintenance, not a speedup claim.
Sum-append is effectively unchanged. Reverse-contract increased 0.93 ms (8%);
unchanged native timings also varied, including reverse-append by 7.6%.
The simplified supporting proofs remain outside the timed declarations.

## Original captured output

Each consecutive group of 14 lines is one run.

```text
LYNX_BENCH erlang/sum-contract 121.45ms
LYNX_BENCH erlang/sum-append 559.27ms
LYNX_BENCH native/sum-append 12.95ms
LYNX_BENCH erlang/reverse-contract 11.34ms
LYNX_BENCH erlang/reverse-involution 8.74ms
LYNX_BENCH erlang/reverse-append 75.60ms
LYNX_BENCH native/reverse-involution 0.82ms
LYNX_BENCH native/reverse-append 5.16ms
LYNX_BENCH erlang/sets-union-contract 77.67ms
LYNX_BENCH erlang/sets-union-commutative 52.55ms
LYNX_BENCH erlang/sets-union-empty 16.68ms
LYNX_BENCH native/sets-union-contract 14.29ms
LYNX_BENCH native/sets-union-commutative 163.63ms
LYNX_BENCH native/sets-union-empty 7.04ms
LYNX_BENCH erlang/sum-contract 123.36ms
LYNX_BENCH erlang/sum-append 556.55ms
LYNX_BENCH native/sum-append 12.88ms
LYNX_BENCH erlang/reverse-contract 11.61ms
LYNX_BENCH erlang/reverse-involution 8.84ms
LYNX_BENCH erlang/reverse-append 75.38ms
LYNX_BENCH native/reverse-involution 0.80ms
LYNX_BENCH native/reverse-append 4.94ms
LYNX_BENCH erlang/sets-union-contract 76.47ms
LYNX_BENCH erlang/sets-union-commutative 49.35ms
LYNX_BENCH erlang/sets-union-empty 16.56ms
LYNX_BENCH native/sets-union-contract 14.75ms
LYNX_BENCH native/sets-union-commutative 166.07ms
LYNX_BENCH native/sets-union-empty 6.20ms
LYNX_BENCH erlang/sum-contract 124.28ms
LYNX_BENCH erlang/sum-append 554.48ms
LYNX_BENCH native/sum-append 13.03ms
LYNX_BENCH erlang/reverse-contract 11.47ms
LYNX_BENCH erlang/reverse-involution 9.77ms
LYNX_BENCH erlang/reverse-append 76.31ms
LYNX_BENCH native/reverse-involution 0.70ms
LYNX_BENCH native/reverse-append 5.54ms
LYNX_BENCH erlang/sets-union-contract 77.29ms
LYNX_BENCH erlang/sets-union-commutative 52.56ms
LYNX_BENCH erlang/sets-union-empty 16.94ms
LYNX_BENCH native/sets-union-contract 13.26ms
LYNX_BENCH native/sets-union-commutative 165.67ms
LYNX_BENCH native/sets-union-empty 6.41ms
LYNX_BENCH erlang/sum-contract 121.45ms
LYNX_BENCH erlang/sum-append 560.59ms
LYNX_BENCH native/sum-append 13.41ms
LYNX_BENCH erlang/reverse-contract 11.64ms
LYNX_BENCH erlang/reverse-involution 9.81ms
LYNX_BENCH erlang/reverse-append 75.80ms
LYNX_BENCH native/reverse-involution 0.70ms
LYNX_BENCH native/reverse-append 5.24ms
LYNX_BENCH erlang/sets-union-contract 77.53ms
LYNX_BENCH erlang/sets-union-commutative 52.41ms
LYNX_BENCH erlang/sets-union-empty 16.13ms
LYNX_BENCH native/sets-union-contract 13.43ms
LYNX_BENCH native/sets-union-commutative 165.20ms
LYNX_BENCH native/sets-union-empty 6.26ms
LYNX_BENCH erlang/sum-contract 124.46ms
LYNX_BENCH erlang/sum-append 555.72ms
LYNX_BENCH native/sum-append 13.16ms
LYNX_BENCH erlang/reverse-contract 12.40ms
LYNX_BENCH erlang/reverse-involution 9.00ms
LYNX_BENCH erlang/reverse-append 75.09ms
LYNX_BENCH native/reverse-involution 0.73ms
LYNX_BENCH native/reverse-append 5.36ms
LYNX_BENCH erlang/sets-union-contract 76.95ms
LYNX_BENCH erlang/sets-union-commutative 52.31ms
LYNX_BENCH erlang/sets-union-empty 16.09ms
LYNX_BENCH native/sets-union-contract 13.12ms
LYNX_BENCH native/sets-union-commutative 166.37ms
LYNX_BENCH native/sets-union-empty 6.24ms
```
