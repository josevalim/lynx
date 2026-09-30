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
| Sum result guarantee | 94.73 | — |
| Sum append | 138.67 | 12.89 |
| Reverse return guarantee | 1.48 | — |
| Reverse involution | 4.59 | 0.76 |
| Reverse append | 29.33 | 4.96 |
| Sets union guarantee | 5.23 | 9.31 |
| Sets union commutativity | 17.77 | 152.49 |
| Sets union empty identity | 5.09 | 5.09 |

## Captured output

Each consecutive group of 14 lines is one run.

```text
LYNX_BENCH erlang/sum-result 94.73ms
LYNX_BENCH erlang/sum-append 138.67ms
LYNX_BENCH native/sum-append 13.28ms
LYNX_BENCH erlang/reverse-result 1.48ms
LYNX_BENCH erlang/reverse-involution 4.63ms
LYNX_BENCH erlang/reverse-append 29.67ms
LYNX_BENCH native/reverse-involution 0.76ms
LYNX_BENCH native/reverse-append 5.28ms
LYNX_BENCH erlang/sets-union-result 5.14ms
LYNX_BENCH erlang/sets-union-commutative 17.51ms
LYNX_BENCH erlang/sets-union-empty 5.22ms
LYNX_BENCH native/sets-union-result 9.10ms
LYNX_BENCH native/sets-union-commutative 152.08ms
LYNX_BENCH native/sets-union-empty 4.81ms
LYNX_BENCH erlang/sum-result 94.82ms
LYNX_BENCH erlang/sum-append 140.60ms
LYNX_BENCH native/sum-append 12.89ms
LYNX_BENCH erlang/reverse-result 1.49ms
LYNX_BENCH erlang/reverse-involution 4.78ms
LYNX_BENCH erlang/reverse-append 29.41ms
LYNX_BENCH native/reverse-involution 0.76ms
LYNX_BENCH native/reverse-append 4.89ms
LYNX_BENCH erlang/sets-union-result 5.08ms
LYNX_BENCH erlang/sets-union-commutative 17.47ms
LYNX_BENCH erlang/sets-union-empty 4.96ms
LYNX_BENCH native/sets-union-result 9.48ms
LYNX_BENCH native/sets-union-commutative 152.49ms
LYNX_BENCH native/sets-union-empty 5.21ms
LYNX_BENCH erlang/sum-result 93.15ms
LYNX_BENCH erlang/sum-append 138.96ms
LYNX_BENCH native/sum-append 12.81ms
LYNX_BENCH erlang/reverse-result 1.41ms
LYNX_BENCH erlang/reverse-involution 4.21ms
LYNX_BENCH erlang/reverse-append 28.52ms
LYNX_BENCH native/reverse-involution 0.83ms
LYNX_BENCH native/reverse-append 4.90ms
LYNX_BENCH erlang/sets-union-result 5.23ms
LYNX_BENCH erlang/sets-union-commutative 17.96ms
LYNX_BENCH erlang/sets-union-empty 5.09ms
LYNX_BENCH native/sets-union-result 9.09ms
LYNX_BENCH native/sets-union-commutative 152.15ms
LYNX_BENCH native/sets-union-empty 5.22ms
LYNX_BENCH erlang/sum-result 91.89ms
LYNX_BENCH erlang/sum-append 137.83ms
LYNX_BENCH native/sum-append 13.34ms
LYNX_BENCH erlang/reverse-result 1.89ms
LYNX_BENCH erlang/reverse-involution 4.39ms
LYNX_BENCH erlang/reverse-append 27.70ms
LYNX_BENCH native/reverse-involution 0.74ms
LYNX_BENCH native/reverse-append 5.27ms
LYNX_BENCH erlang/sets-union-result 5.45ms
LYNX_BENCH erlang/sets-union-commutative 18.13ms
LYNX_BENCH erlang/sets-union-empty 5.24ms
LYNX_BENCH native/sets-union-result 9.31ms
LYNX_BENCH native/sets-union-commutative 154.14ms
LYNX_BENCH native/sets-union-empty 5.09ms
LYNX_BENCH erlang/sum-result 96.07ms
LYNX_BENCH erlang/sum-append 136.15ms
LYNX_BENCH native/sum-append 12.11ms
LYNX_BENCH erlang/reverse-result 1.39ms
LYNX_BENCH erlang/reverse-involution 4.59ms
LYNX_BENCH erlang/reverse-append 29.33ms
LYNX_BENCH native/reverse-involution 0.76ms
LYNX_BENCH native/reverse-append 4.96ms
LYNX_BENCH erlang/sets-union-result 5.39ms
LYNX_BENCH erlang/sets-union-commutative 17.77ms
LYNX_BENCH erlang/sets-union-empty 4.87ms
LYNX_BENCH native/sets-union-result 10.22ms
LYNX_BENCH native/sets-union-commutative 153.30ms
LYNX_BENCH native/sets-union-empty 5.03ms
```
