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
| Sum result guarantee | 213.25 | — |
| Sum append | 257.57 | 13.11 |
| Reverse return guarantee | 1.48 | — |
| Reverse involution | 4.62 | 0.74 |
| Reverse append | 29.45 | 5.54 |
| Sets union guarantee | 5.30 | 9.55 |
| Sets union commutativity | 18.01 | 156.35 |
| Sets union empty identity | 5.62 | 5.06 |

## Captured output

Each consecutive group of 14 lines is one run.

```text
LYNX_BENCH erlang/sum-result 215.12ms
LYNX_BENCH erlang/sum-append 257.57ms
LYNX_BENCH native/sum-append 13.41ms
LYNX_BENCH erlang/reverse-result 1.42ms
LYNX_BENCH erlang/reverse-involution 4.82ms
LYNX_BENCH erlang/reverse-append 29.45ms
LYNX_BENCH native/reverse-involution 0.74ms
LYNX_BENCH native/reverse-append 4.84ms
LYNX_BENCH erlang/sets-union-result 5.30ms
LYNX_BENCH erlang/sets-union-commutative 17.84ms
LYNX_BENCH erlang/sets-union-empty 5.62ms
LYNX_BENCH native/sets-union-result 9.46ms
LYNX_BENCH native/sets-union-commutative 149.39ms
LYNX_BENCH native/sets-union-empty 4.85ms
LYNX_BENCH erlang/sum-result 204.16ms
LYNX_BENCH erlang/sum-append 251.81ms
LYNX_BENCH native/sum-append 12.39ms
LYNX_BENCH erlang/reverse-result 1.48ms
LYNX_BENCH erlang/reverse-involution 4.43ms
LYNX_BENCH erlang/reverse-append 27.77ms
LYNX_BENCH native/reverse-involution 0.75ms
LYNX_BENCH native/reverse-append 5.10ms
LYNX_BENCH erlang/sets-union-result 5.33ms
LYNX_BENCH erlang/sets-union-commutative 17.45ms
LYNX_BENCH erlang/sets-union-empty 5.58ms
LYNX_BENCH native/sets-union-result 9.12ms
LYNX_BENCH native/sets-union-commutative 156.35ms
LYNX_BENCH native/sets-union-empty 5.06ms
LYNX_BENCH erlang/sum-result 205.40ms
LYNX_BENCH erlang/sum-append 255.30ms
LYNX_BENCH native/sum-append 13.11ms
LYNX_BENCH erlang/reverse-result 1.46ms
LYNX_BENCH erlang/reverse-involution 4.25ms
LYNX_BENCH erlang/reverse-append 29.86ms
LYNX_BENCH native/reverse-involution 0.74ms
LYNX_BENCH native/reverse-append 5.54ms
LYNX_BENCH erlang/sets-union-result 5.21ms
LYNX_BENCH erlang/sets-union-commutative 18.01ms
LYNX_BENCH erlang/sets-union-empty 5.30ms
LYNX_BENCH native/sets-union-result 9.55ms
LYNX_BENCH native/sets-union-commutative 150.73ms
LYNX_BENCH native/sets-union-empty 4.85ms
LYNX_BENCH erlang/sum-result 215.02ms
LYNX_BENCH erlang/sum-append 266.48ms
LYNX_BENCH native/sum-append 12.65ms
LYNX_BENCH erlang/reverse-result 1.57ms
LYNX_BENCH erlang/reverse-involution 4.62ms
LYNX_BENCH erlang/reverse-append 29.20ms
LYNX_BENCH native/reverse-involution 0.75ms
LYNX_BENCH native/reverse-append 5.59ms
LYNX_BENCH erlang/sets-union-result 5.21ms
LYNX_BENCH erlang/sets-union-commutative 18.34ms
LYNX_BENCH erlang/sets-union-empty 5.66ms
LYNX_BENCH native/sets-union-result 10.75ms
LYNX_BENCH native/sets-union-commutative 157.63ms
LYNX_BENCH native/sets-union-empty 5.19ms
LYNX_BENCH erlang/sum-result 213.25ms
LYNX_BENCH erlang/sum-append 273.64ms
LYNX_BENCH native/sum-append 14.28ms
LYNX_BENCH erlang/reverse-result 1.48ms
LYNX_BENCH erlang/reverse-involution 4.82ms
LYNX_BENCH erlang/reverse-append 30.28ms
LYNX_BENCH native/reverse-involution 0.74ms
LYNX_BENCH native/reverse-append 6.18ms
LYNX_BENCH erlang/sets-union-result 5.55ms
LYNX_BENCH erlang/sets-union-commutative 18.29ms
LYNX_BENCH erlang/sets-union-empty 5.70ms
LYNX_BENCH native/sets-union-result 10.20ms
LYNX_BENCH native/sets-union-commutative 160.07ms
LYNX_BENCH native/sets-union-empty 5.07ms
```
