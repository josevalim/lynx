# Benchmark results

Captured on 2026-09-10 with Lean 4.33.1 on macOS arm64.

```sh
sh Benchmarks/run.sh 3
```

All 18 fresh Lean processes and 42 timed declarations passed.
Times are median proof-elaboration milliseconds, not executable runtime.
Measurements exclude imports and supporting lemmas; later proofs in each file
may reuse earlier results and cached summaries.

| Target | Translated (ms) | Native (ms) |
| --- | ---: | ---: |
| Sum result contract | 177.73 | — |
| Sum append | 541.83 | 11.69 |
| Reverse return contract | 10.63 | — |
| Reverse involution | 6.81 | 0.70 |
| Reverse append | 80.11 | 4.52 |
| Sets union contract | 68.85 | 11.90 |
| Sets union commutativity | 48.07 | 143.21 |
| Sets union empty identity | 17.08 | 5.22 |

## Captured output

Each consecutive group of 14 lines is one run.

```text
LYNX_BENCH erlang/sum-contract 177.73ms
LYNX_BENCH erlang/sum-append 541.83ms
LYNX_BENCH native/sum-append 11.75ms
LYNX_BENCH erlang/reverse-contract 10.73ms
LYNX_BENCH erlang/reverse-involution 6.81ms
LYNX_BENCH erlang/reverse-append 80.32ms
LYNX_BENCH native/reverse-involution 0.70ms
LYNX_BENCH native/reverse-append 4.52ms
LYNX_BENCH erlang/sets-union-contract 68.18ms
LYNX_BENCH erlang/sets-union-commutative 47.33ms
LYNX_BENCH erlang/sets-union-empty 16.86ms
LYNX_BENCH native/sets-union-contract 11.90ms
LYNX_BENCH native/sets-union-commutative 143.21ms
LYNX_BENCH native/sets-union-empty 5.22ms
LYNX_BENCH erlang/sum-contract 177.49ms
LYNX_BENCH erlang/sum-append 541.41ms
LYNX_BENCH native/sum-append 11.44ms
LYNX_BENCH erlang/reverse-contract 10.50ms
LYNX_BENCH erlang/reverse-involution 7.02ms
LYNX_BENCH erlang/reverse-append 79.77ms
LYNX_BENCH native/reverse-involution 0.68ms
LYNX_BENCH native/reverse-append 4.48ms
LYNX_BENCH erlang/sets-union-contract 71.54ms
LYNX_BENCH erlang/sets-union-commutative 49.97ms
LYNX_BENCH erlang/sets-union-empty 17.75ms
LYNX_BENCH native/sets-union-contract 11.97ms
LYNX_BENCH native/sets-union-commutative 143.01ms
LYNX_BENCH native/sets-union-empty 5.19ms
LYNX_BENCH erlang/sum-contract 183.03ms
LYNX_BENCH erlang/sum-append 550.65ms
LYNX_BENCH native/sum-append 11.69ms
LYNX_BENCH erlang/reverse-contract 10.63ms
LYNX_BENCH erlang/reverse-involution 6.81ms
LYNX_BENCH erlang/reverse-append 80.11ms
LYNX_BENCH native/reverse-involution 0.70ms
LYNX_BENCH native/reverse-append 4.53ms
LYNX_BENCH erlang/sets-union-contract 68.85ms
LYNX_BENCH erlang/sets-union-commutative 48.07ms
LYNX_BENCH erlang/sets-union-empty 17.08ms
LYNX_BENCH native/sets-union-contract 11.87ms
LYNX_BENCH native/sets-union-commutative 145.96ms
LYNX_BENCH native/sets-union-empty 5.56ms
```
