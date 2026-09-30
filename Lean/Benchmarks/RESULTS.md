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
| Sum result guarantee | 72.11 | — |
| Sum append | 114.61 | 12.73 |
| Reverse return guarantee | 1.42 | — |
| Reverse involution | 4.24 | 0.75 |
| Reverse append | 27.44 | 4.83 |
| Sets union guarantee | 5.18 | 9.14 |
| Sets union commutativity | 17.98 | 150.32 |
| Sets union empty identity | 4.92 | 4.97 |

## Captured output

Each consecutive group of 14 lines is one run.

```text
LYNX_BENCH erlang/sum-result 72.12ms
LYNX_BENCH erlang/sum-append 115.01ms
LYNX_BENCH native/sum-append 12.91ms
LYNX_BENCH erlang/reverse-result 1.39ms
LYNX_BENCH erlang/reverse-involution 4.21ms
LYNX_BENCH erlang/reverse-append 27.44ms
LYNX_BENCH native/reverse-involution 0.73ms
LYNX_BENCH native/reverse-append 4.87ms
LYNX_BENCH erlang/sets-union-result 5.05ms
LYNX_BENCH erlang/sets-union-commutative 17.98ms
LYNX_BENCH erlang/sets-union-empty 5.01ms
LYNX_BENCH native/sets-union-result 8.88ms
LYNX_BENCH native/sets-union-commutative 149.11ms
LYNX_BENCH native/sets-union-empty 4.86ms
LYNX_BENCH erlang/sum-result 71.45ms
LYNX_BENCH erlang/sum-append 115.48ms
LYNX_BENCH native/sum-append 12.27ms
LYNX_BENCH erlang/reverse-result 1.42ms
LYNX_BENCH erlang/reverse-involution 4.24ms
LYNX_BENCH erlang/reverse-append 27.68ms
LYNX_BENCH native/reverse-involution 0.75ms
LYNX_BENCH native/reverse-append 4.83ms
LYNX_BENCH erlang/sets-union-result 5.41ms
LYNX_BENCH erlang/sets-union-commutative 18.10ms
LYNX_BENCH erlang/sets-union-empty 4.92ms
LYNX_BENCH native/sets-union-result 9.14ms
LYNX_BENCH native/sets-union-commutative 150.32ms
LYNX_BENCH native/sets-union-empty 5.01ms
LYNX_BENCH erlang/sum-result 72.11ms
LYNX_BENCH erlang/sum-append 114.61ms
LYNX_BENCH native/sum-append 12.73ms
LYNX_BENCH erlang/reverse-result 1.47ms
LYNX_BENCH erlang/reverse-involution 4.24ms
LYNX_BENCH erlang/reverse-append 27.76ms
LYNX_BENCH native/reverse-involution 0.87ms
LYNX_BENCH native/reverse-append 4.80ms
LYNX_BENCH erlang/sets-union-result 5.18ms
LYNX_BENCH erlang/sets-union-commutative 17.72ms
LYNX_BENCH erlang/sets-union-empty 5.20ms
LYNX_BENCH native/sets-union-result 9.05ms
LYNX_BENCH native/sets-union-commutative 152.94ms
LYNX_BENCH native/sets-union-empty 5.09ms
LYNX_BENCH erlang/sum-result 71.04ms
LYNX_BENCH erlang/sum-append 114.33ms
LYNX_BENCH native/sum-append 12.27ms
LYNX_BENCH erlang/reverse-result 1.38ms
LYNX_BENCH erlang/reverse-involution 4.13ms
LYNX_BENCH erlang/reverse-append 27.41ms
LYNX_BENCH native/reverse-involution 0.72ms
LYNX_BENCH native/reverse-append 4.83ms
LYNX_BENCH erlang/sets-union-result 5.27ms
LYNX_BENCH erlang/sets-union-commutative 17.90ms
LYNX_BENCH erlang/sets-union-empty 4.82ms
LYNX_BENCH native/sets-union-result 9.88ms
LYNX_BENCH native/sets-union-commutative 150.55ms
LYNX_BENCH native/sets-union-empty 4.97ms
LYNX_BENCH erlang/sum-result 74.57ms
LYNX_BENCH erlang/sum-append 114.19ms
LYNX_BENCH native/sum-append 13.13ms
LYNX_BENCH erlang/reverse-result 1.48ms
LYNX_BENCH erlang/reverse-involution 4.34ms
LYNX_BENCH erlang/reverse-append 27.40ms
LYNX_BENCH native/reverse-involution 0.84ms
LYNX_BENCH native/reverse-append 4.93ms
LYNX_BENCH erlang/sets-union-result 5.16ms
LYNX_BENCH erlang/sets-union-commutative 18.41ms
LYNX_BENCH erlang/sets-union-empty 4.82ms
LYNX_BENCH native/sets-union-result 9.99ms
LYNX_BENCH native/sets-union-commutative 150.07ms
LYNX_BENCH native/sets-union-empty 4.96ms
```
