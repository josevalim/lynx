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
| Sum result guarantee | 114.47 | — |
| Sum append | 161.98 | 13.08 |
| Reverse return guarantee | 1.40 | — |
| Reverse involution | 4.49 | 0.81 |
| Reverse append | 30.02 | 5.24 |
| Sets union guarantee | 5.39 | 10.56 |
| Sets union commutativity | 18.80 | 159.83 |
| Sets union empty identity | 5.29 | 5.05 |

## Captured output

Each consecutive group of 14 lines is one run.

```text
LYNX_BENCH erlang/sum-result 114.47ms
LYNX_BENCH erlang/sum-append 158.79ms
LYNX_BENCH native/sum-append 13.08ms
LYNX_BENCH erlang/reverse-result 1.39ms
LYNX_BENCH erlang/reverse-involution 4.34ms
LYNX_BENCH erlang/reverse-append 30.55ms
LYNX_BENCH native/reverse-involution 0.84ms
LYNX_BENCH native/reverse-append 4.97ms
LYNX_BENCH erlang/sets-union-result 5.23ms
LYNX_BENCH erlang/sets-union-commutative 19.07ms
LYNX_BENCH erlang/sets-union-empty 5.11ms
LYNX_BENCH native/sets-union-result 11.32ms
LYNX_BENCH native/sets-union-commutative 155.86ms
LYNX_BENCH native/sets-union-empty 5.05ms
LYNX_BENCH erlang/sum-result 114.66ms
LYNX_BENCH erlang/sum-append 161.98ms
LYNX_BENCH native/sum-append 12.41ms
LYNX_BENCH erlang/reverse-result 1.37ms
LYNX_BENCH erlang/reverse-involution 4.49ms
LYNX_BENCH erlang/reverse-append 30.02ms
LYNX_BENCH native/reverse-involution 0.81ms
LYNX_BENCH native/reverse-append 5.45ms
LYNX_BENCH erlang/sets-union-result 5.48ms
LYNX_BENCH erlang/sets-union-commutative 18.80ms
LYNX_BENCH erlang/sets-union-empty 5.17ms
LYNX_BENCH native/sets-union-result 9.84ms
LYNX_BENCH native/sets-union-commutative 159.83ms
LYNX_BENCH native/sets-union-empty 5.45ms
LYNX_BENCH erlang/sum-result 114.07ms
LYNX_BENCH erlang/sum-append 161.88ms
LYNX_BENCH native/sum-append 13.27ms
LYNX_BENCH erlang/reverse-result 1.64ms
LYNX_BENCH erlang/reverse-involution 5.04ms
LYNX_BENCH erlang/reverse-append 30.19ms
LYNX_BENCH native/reverse-involution 0.93ms
LYNX_BENCH native/reverse-append 5.24ms
LYNX_BENCH erlang/sets-union-result 6.05ms
LYNX_BENCH erlang/sets-union-commutative 18.98ms
LYNX_BENCH erlang/sets-union-empty 5.29ms
LYNX_BENCH native/sets-union-result 9.09ms
LYNX_BENCH native/sets-union-commutative 162.04ms
LYNX_BENCH native/sets-union-empty 5.05ms
LYNX_BENCH erlang/sum-result 117.93ms
LYNX_BENCH erlang/sum-append 164.03ms
LYNX_BENCH native/sum-append 14.54ms
LYNX_BENCH erlang/reverse-result 1.40ms
LYNX_BENCH erlang/reverse-involution 4.63ms
LYNX_BENCH erlang/reverse-append 28.95ms
LYNX_BENCH native/reverse-involution 0.80ms
LYNX_BENCH native/reverse-append 5.08ms
LYNX_BENCH erlang/sets-union-result 5.39ms
LYNX_BENCH erlang/sets-union-commutative 18.62ms
LYNX_BENCH erlang/sets-union-empty 5.42ms
LYNX_BENCH native/sets-union-result 10.64ms
LYNX_BENCH native/sets-union-commutative 163.11ms
LYNX_BENCH native/sets-union-empty 4.96ms
LYNX_BENCH erlang/sum-result 113.53ms
LYNX_BENCH erlang/sum-append 163.09ms
LYNX_BENCH native/sum-append 12.77ms
LYNX_BENCH erlang/reverse-result 1.42ms
LYNX_BENCH erlang/reverse-involution 4.31ms
LYNX_BENCH erlang/reverse-append 27.50ms
LYNX_BENCH native/reverse-involution 0.73ms
LYNX_BENCH native/reverse-append 6.48ms
LYNX_BENCH erlang/sets-union-result 5.24ms
LYNX_BENCH erlang/sets-union-commutative 18.74ms
LYNX_BENCH erlang/sets-union-empty 5.36ms
LYNX_BENCH native/sets-union-result 10.56ms
LYNX_BENCH native/sets-union-commutative 152.56ms
LYNX_BENCH native/sets-union-empty 5.11ms
```
