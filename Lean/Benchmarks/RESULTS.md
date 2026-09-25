# Benchmark results

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
