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
| Sum result guarantee | 110.85 | — |
| Sum append | 153.61 | 12.68 |
| Reverse return guarantee | 1.42 | — |
| Reverse involution | 4.51 | 0.76 |
| Reverse append | 27.91 | 4.84 |
| Sets union guarantee | 5.07 | 10.34 |
| Sets union commutativity | 18.08 | 154.83 |
| Sets union empty identity | 5.62 | 5.59 |

## Captured output

Each consecutive group of 14 lines is one run.

```text
LYNX_BENCH erlang/sum-result 110.85ms
LYNX_BENCH erlang/sum-append 152.11ms
LYNX_BENCH native/sum-append 13.19ms
LYNX_BENCH erlang/reverse-result 1.42ms
LYNX_BENCH erlang/reverse-involution 4.51ms
LYNX_BENCH erlang/reverse-append 27.99ms
LYNX_BENCH native/reverse-involution 0.75ms
LYNX_BENCH native/reverse-append 4.83ms
LYNX_BENCH erlang/sets-union-result 5.14ms
LYNX_BENCH erlang/sets-union-commutative 17.78ms
LYNX_BENCH erlang/sets-union-empty 6.18ms
LYNX_BENCH native/sets-union-result 9.44ms
LYNX_BENCH native/sets-union-commutative 152.24ms
LYNX_BENCH native/sets-union-empty 5.64ms
LYNX_BENCH erlang/sum-result 110.09ms
LYNX_BENCH erlang/sum-append 150.54ms
LYNX_BENCH native/sum-append 12.36ms
LYNX_BENCH erlang/reverse-result 1.39ms
LYNX_BENCH erlang/reverse-involution 4.46ms
LYNX_BENCH erlang/reverse-append 27.63ms
LYNX_BENCH native/reverse-involution 0.73ms
LYNX_BENCH native/reverse-append 4.81ms
LYNX_BENCH erlang/sets-union-result 4.97ms
LYNX_BENCH erlang/sets-union-commutative 18.08ms
LYNX_BENCH erlang/sets-union-empty 5.62ms
LYNX_BENCH native/sets-union-result 10.51ms
LYNX_BENCH native/sets-union-commutative 161.49ms
LYNX_BENCH native/sets-union-empty 5.97ms
LYNX_BENCH erlang/sum-result 113.43ms
LYNX_BENCH erlang/sum-append 153.61ms
LYNX_BENCH native/sum-append 12.68ms
LYNX_BENCH erlang/reverse-result 1.68ms
LYNX_BENCH erlang/reverse-involution 4.56ms
LYNX_BENCH erlang/reverse-append 28.66ms
LYNX_BENCH native/reverse-involution 0.88ms
LYNX_BENCH native/reverse-append 5.72ms
LYNX_BENCH erlang/sets-union-result 5.07ms
LYNX_BENCH erlang/sets-union-commutative 18.35ms
LYNX_BENCH erlang/sets-union-empty 6.01ms
LYNX_BENCH native/sets-union-result 10.34ms
LYNX_BENCH native/sets-union-commutative 154.83ms
LYNX_BENCH native/sets-union-empty 5.38ms
LYNX_BENCH erlang/sum-result 108.23ms
LYNX_BENCH erlang/sum-append 157.90ms
LYNX_BENCH native/sum-append 12.27ms
LYNX_BENCH erlang/reverse-result 1.43ms
LYNX_BENCH erlang/reverse-involution 4.64ms
LYNX_BENCH erlang/reverse-append 27.91ms
LYNX_BENCH native/reverse-involution 0.84ms
LYNX_BENCH native/reverse-append 6.05ms
LYNX_BENCH erlang/sets-union-result 5.14ms
LYNX_BENCH erlang/sets-union-commutative 17.67ms
LYNX_BENCH erlang/sets-union-empty 5.18ms
LYNX_BENCH native/sets-union-result 10.41ms
LYNX_BENCH native/sets-union-commutative 164.67ms
LYNX_BENCH native/sets-union-empty 5.33ms
LYNX_BENCH erlang/sum-result 120.70ms
LYNX_BENCH erlang/sum-append 169.21ms
LYNX_BENCH native/sum-append 12.68ms
LYNX_BENCH erlang/reverse-result 1.40ms
LYNX_BENCH erlang/reverse-involution 4.47ms
LYNX_BENCH erlang/reverse-append 27.66ms
LYNX_BENCH native/reverse-involution 0.76ms
LYNX_BENCH native/reverse-append 4.84ms
LYNX_BENCH erlang/sets-union-result 5.06ms
LYNX_BENCH erlang/sets-union-commutative 19.13ms
LYNX_BENCH erlang/sets-union-empty 5.12ms
LYNX_BENCH native/sets-union-result 8.92ms
LYNX_BENCH native/sets-union-commutative 151.33ms
LYNX_BENCH native/sets-union-empty 5.59ms
```
