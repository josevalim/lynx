# Benchmark results

Captured on 2026-10-01 with Lean 4.33.1 on macOS arm64.

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
| Sum result guarantee | 23.64 | — |
| Sum append | 65.23 | 13.60 |
| Reverse return guarantee | 1.61 | — |
| Reverse involution | 4.68 | 0.91 |
| Reverse append | 30.54 | 5.80 |
| Sets union guarantee | 5.27 | 9.96 |
| Sets union commutativity | 18.50 | 163.14 |
| Sets union empty identity | 5.52 | 5.69 |

## Captured output

Each consecutive group of 14 lines is one run.

```text
LYNX_BENCH erlang/sum-result 22.85ms
LYNX_BENCH erlang/sum-append 63.51ms
LYNX_BENCH native/sum-append 13.60ms
LYNX_BENCH erlang/reverse-result 1.61ms
LYNX_BENCH erlang/reverse-involution 4.60ms
LYNX_BENCH erlang/reverse-append 29.97ms
LYNX_BENCH native/reverse-involution 0.77ms
LYNX_BENCH native/reverse-append 5.83ms
LYNX_BENCH erlang/sets-union-result 6.07ms
LYNX_BENCH erlang/sets-union-commutative 18.50ms
LYNX_BENCH erlang/sets-union-empty 5.52ms
LYNX_BENCH native/sets-union-result 10.43ms
LYNX_BENCH native/sets-union-commutative 164.02ms
LYNX_BENCH native/sets-union-empty 5.69ms
LYNX_BENCH erlang/sum-result 25.44ms
LYNX_BENCH erlang/sum-append 63.74ms
LYNX_BENCH native/sum-append 13.25ms
LYNX_BENCH erlang/reverse-result 1.66ms
LYNX_BENCH erlang/reverse-involution 4.68ms
LYNX_BENCH erlang/reverse-append 29.63ms
LYNX_BENCH native/reverse-involution 0.91ms
LYNX_BENCH native/reverse-append 5.05ms
LYNX_BENCH erlang/sets-union-result 5.27ms
LYNX_BENCH erlang/sets-union-commutative 18.24ms
LYNX_BENCH erlang/sets-union-empty 5.05ms
LYNX_BENCH native/sets-union-result 9.97ms
LYNX_BENCH native/sets-union-commutative 162.96ms
LYNX_BENCH native/sets-union-empty 5.45ms
LYNX_BENCH erlang/sum-result 23.10ms
LYNX_BENCH erlang/sum-append 65.23ms
LYNX_BENCH native/sum-append 14.20ms
LYNX_BENCH erlang/reverse-result 1.92ms
LYNX_BENCH erlang/reverse-involution 5.96ms
LYNX_BENCH erlang/reverse-append 33.19ms
LYNX_BENCH native/reverse-involution 1.13ms
LYNX_BENCH native/reverse-append 5.65ms
LYNX_BENCH erlang/sets-union-result 5.71ms
LYNX_BENCH erlang/sets-union-commutative 19.18ms
LYNX_BENCH erlang/sets-union-empty 5.86ms
LYNX_BENCH native/sets-union-result 9.96ms
LYNX_BENCH native/sets-union-commutative 159.75ms
LYNX_BENCH native/sets-union-empty 5.24ms
LYNX_BENCH erlang/sum-result 25.32ms
LYNX_BENCH erlang/sum-append 68.01ms
LYNX_BENCH native/sum-append 13.69ms
LYNX_BENCH erlang/reverse-result 1.50ms
LYNX_BENCH erlang/reverse-involution 4.51ms
LYNX_BENCH erlang/reverse-append 30.54ms
LYNX_BENCH native/reverse-involution 0.75ms
LYNX_BENCH native/reverse-append 5.92ms
LYNX_BENCH erlang/sets-union-result 5.16ms
LYNX_BENCH erlang/sets-union-commutative 19.55ms
LYNX_BENCH erlang/sets-union-empty 6.03ms
LYNX_BENCH native/sets-union-result 9.91ms
LYNX_BENCH native/sets-union-commutative 163.14ms
LYNX_BENCH native/sets-union-empty 5.88ms
LYNX_BENCH erlang/sum-result 23.64ms
LYNX_BENCH erlang/sum-append 66.64ms
LYNX_BENCH native/sum-append 13.31ms
LYNX_BENCH erlang/reverse-result 1.60ms
LYNX_BENCH erlang/reverse-involution 5.08ms
LYNX_BENCH erlang/reverse-append 34.17ms
LYNX_BENCH native/reverse-involution 0.93ms
LYNX_BENCH native/reverse-append 5.80ms
LYNX_BENCH erlang/sets-union-result 5.16ms
LYNX_BENCH erlang/sets-union-commutative 18.17ms
LYNX_BENCH erlang/sets-union-empty 5.46ms
LYNX_BENCH native/sets-union-result 9.31ms
LYNX_BENCH native/sets-union-commutative 163.22ms
LYNX_BENCH native/sets-union-empty 6.49ms
```
