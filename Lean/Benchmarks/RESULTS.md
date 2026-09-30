# Benchmark results

Captured on 2026-09-30 with Lean 4.33.1 on macOS arm64.

```sh
sh Benchmarks/run.sh 5
```

All 30 fresh Lean processes and 70 timed declarations passed.
Times are median proof-elaboration milliseconds, not executable runtime.
Measurements exclude imports and supporting lemmas; later proofs in each file
may reuse earlier theorems.
Each suite includes the Elixir implementation and separate `law` comments,
followed by translated computations and handwritten proofs with explicit
assumptions. The theorem statements do not use contract wrappers.

| Target | Translated (ms) | Native (ms) |
| --- | ---: | ---: |
| Sum result guarantee | 77.17 | — |
| Sum append | 122.40 | 13.22 |
| Reverse return guarantee | 1.66 | — |
| Reverse involution | 4.53 | 0.80 |
| Reverse append | 29.44 | 5.45 |
| Sets union guarantee | 5.23 | 10.12 |
| Sets union commutativity | 18.93 | 159.74 |
| Sets union empty identity | 5.26 | 5.35 |

## Captured output

Each consecutive group of 14 lines is one run.

```text
LYNX_BENCH erlang/sum-result 78.86ms
LYNX_BENCH erlang/sum-append 121.25ms
LYNX_BENCH native/sum-append 13.56ms
LYNX_BENCH erlang/reverse-result 1.49ms
LYNX_BENCH erlang/reverse-involution 4.36ms
LYNX_BENCH erlang/reverse-append 29.09ms
LYNX_BENCH native/reverse-involution 0.76ms
LYNX_BENCH native/reverse-append 5.89ms
LYNX_BENCH erlang/sets-union-result 5.23ms
LYNX_BENCH erlang/sets-union-commutative 18.90ms
LYNX_BENCH erlang/sets-union-empty 5.00ms
LYNX_BENCH native/sets-union-result 10.14ms
LYNX_BENCH native/sets-union-commutative 160.25ms
LYNX_BENCH native/sets-union-empty 5.14ms
LYNX_BENCH erlang/sum-result 76.12ms
LYNX_BENCH erlang/sum-append 122.80ms
LYNX_BENCH native/sum-append 13.64ms
LYNX_BENCH erlang/reverse-result 1.66ms
LYNX_BENCH erlang/reverse-involution 4.58ms
LYNX_BENCH erlang/reverse-append 29.78ms
LYNX_BENCH native/reverse-involution 0.83ms
LYNX_BENCH native/reverse-append 5.05ms
LYNX_BENCH erlang/sets-union-result 5.20ms
LYNX_BENCH erlang/sets-union-commutative 18.94ms
LYNX_BENCH erlang/sets-union-empty 5.48ms
LYNX_BENCH native/sets-union-result 9.82ms
LYNX_BENCH native/sets-union-commutative 157.16ms
LYNX_BENCH native/sets-union-empty 5.35ms
LYNX_BENCH erlang/sum-result 77.66ms
LYNX_BENCH erlang/sum-append 122.40ms
LYNX_BENCH native/sum-append 12.79ms
LYNX_BENCH erlang/reverse-result 1.70ms
LYNX_BENCH erlang/reverse-involution 4.53ms
LYNX_BENCH erlang/reverse-append 29.40ms
LYNX_BENCH native/reverse-involution 0.80ms
LYNX_BENCH native/reverse-append 5.93ms
LYNX_BENCH erlang/sets-union-result 5.55ms
LYNX_BENCH erlang/sets-union-commutative 18.93ms
LYNX_BENCH erlang/sets-union-empty 4.92ms
LYNX_BENCH native/sets-union-result 9.17ms
LYNX_BENCH native/sets-union-commutative 160.91ms
LYNX_BENCH native/sets-union-empty 5.44ms
LYNX_BENCH erlang/sum-result 75.47ms
LYNX_BENCH erlang/sum-append 121.96ms
LYNX_BENCH native/sum-append 13.22ms
LYNX_BENCH erlang/reverse-result 1.68ms
LYNX_BENCH erlang/reverse-involution 4.70ms
LYNX_BENCH erlang/reverse-append 29.72ms
LYNX_BENCH native/reverse-involution 0.79ms
LYNX_BENCH native/reverse-append 5.23ms
LYNX_BENCH erlang/sets-union-result 5.32ms
LYNX_BENCH erlang/sets-union-commutative 18.97ms
LYNX_BENCH erlang/sets-union-empty 5.26ms
LYNX_BENCH native/sets-union-result 10.12ms
LYNX_BENCH native/sets-union-commutative 159.74ms
LYNX_BENCH native/sets-union-empty 5.60ms
LYNX_BENCH erlang/sum-result 77.17ms
LYNX_BENCH erlang/sum-append 125.11ms
LYNX_BENCH native/sum-append 13.13ms
LYNX_BENCH erlang/reverse-result 1.44ms
LYNX_BENCH erlang/reverse-involution 4.48ms
LYNX_BENCH erlang/reverse-append 29.44ms
LYNX_BENCH native/reverse-involution 1.16ms
LYNX_BENCH native/reverse-append 5.45ms
LYNX_BENCH erlang/sets-union-result 5.02ms
LYNX_BENCH erlang/sets-union-commutative 18.58ms
LYNX_BENCH erlang/sets-union-empty 5.26ms
LYNX_BENCH native/sets-union-result 10.43ms
LYNX_BENCH native/sets-union-commutative 156.27ms
LYNX_BENCH native/sets-union-empty 4.86ms
```
