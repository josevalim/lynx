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
| Sum result guarantee | 113.99 | — |
| Sum append | 161.35 | 13.22 |
| Reverse return guarantee | 1.41 | — |
| Reverse involution | 4.53 | 0.83 |
| Reverse append | 29.79 | 5.52 |
| Sets union guarantee | 5.11 | 10.41 |
| Sets union commutativity | 18.27 | 152.78 |
| Sets union empty identity | 5.60 | 5.23 |

## Captured output

Each consecutive group of 14 lines is one run.

```text
LYNX_BENCH erlang/sum-result 119.49ms
LYNX_BENCH erlang/sum-append 170.65ms
LYNX_BENCH native/sum-append 13.86ms
LYNX_BENCH erlang/reverse-result 1.78ms
LYNX_BENCH erlang/reverse-involution 4.67ms
LYNX_BENCH erlang/reverse-append 28.73ms
LYNX_BENCH native/reverse-involution 1.19ms
LYNX_BENCH native/reverse-append 5.52ms
LYNX_BENCH erlang/sets-union-result 4.95ms
LYNX_BENCH erlang/sets-union-commutative 19.95ms
LYNX_BENCH erlang/sets-union-empty 5.93ms
LYNX_BENCH native/sets-union-result 10.60ms
LYNX_BENCH native/sets-union-commutative 158.30ms
LYNX_BENCH native/sets-union-empty 5.23ms
LYNX_BENCH erlang/sum-result 113.99ms
LYNX_BENCH erlang/sum-append 161.35ms
LYNX_BENCH native/sum-append 12.31ms
LYNX_BENCH erlang/reverse-result 1.41ms
LYNX_BENCH erlang/reverse-involution 4.47ms
LYNX_BENCH erlang/reverse-append 30.08ms
LYNX_BENCH native/reverse-involution 0.76ms
LYNX_BENCH native/reverse-append 6.09ms
LYNX_BENCH erlang/sets-union-result 5.05ms
LYNX_BENCH erlang/sets-union-commutative 18.19ms
LYNX_BENCH erlang/sets-union-empty 5.41ms
LYNX_BENCH native/sets-union-result 9.29ms
LYNX_BENCH native/sets-union-commutative 152.78ms
LYNX_BENCH native/sets-union-empty 6.22ms
LYNX_BENCH erlang/sum-result 108.62ms
LYNX_BENCH erlang/sum-append 151.24ms
LYNX_BENCH native/sum-append 13.22ms
LYNX_BENCH erlang/reverse-result 1.40ms
LYNX_BENCH erlang/reverse-involution 4.44ms
LYNX_BENCH erlang/reverse-append 27.88ms
LYNX_BENCH native/reverse-involution 0.77ms
LYNX_BENCH native/reverse-append 5.06ms
LYNX_BENCH erlang/sets-union-result 5.11ms
LYNX_BENCH erlang/sets-union-commutative 18.23ms
LYNX_BENCH erlang/sets-union-empty 5.60ms
LYNX_BENCH native/sets-union-result 10.41ms
LYNX_BENCH native/sets-union-commutative 149.49ms
LYNX_BENCH native/sets-union-empty 5.00ms
LYNX_BENCH erlang/sum-result 109.83ms
LYNX_BENCH erlang/sum-append 154.11ms
LYNX_BENCH native/sum-append 12.82ms
LYNX_BENCH erlang/reverse-result 1.37ms
LYNX_BENCH erlang/reverse-involution 4.53ms
LYNX_BENCH erlang/reverse-append 29.79ms
LYNX_BENCH native/reverse-involution 0.83ms
LYNX_BENCH native/reverse-append 4.95ms
LYNX_BENCH erlang/sets-union-result 5.21ms
LYNX_BENCH erlang/sets-union-commutative 18.27ms
LYNX_BENCH erlang/sets-union-empty 5.00ms
LYNX_BENCH native/sets-union-result 9.73ms
LYNX_BENCH native/sets-union-commutative 149.03ms
LYNX_BENCH native/sets-union-empty 4.84ms
LYNX_BENCH erlang/sum-result 114.91ms
LYNX_BENCH erlang/sum-append 162.42ms
LYNX_BENCH native/sum-append 13.86ms
LYNX_BENCH erlang/reverse-result 1.60ms
LYNX_BENCH erlang/reverse-involution 4.95ms
LYNX_BENCH erlang/reverse-append 31.05ms
LYNX_BENCH native/reverse-involution 0.94ms
LYNX_BENCH native/reverse-append 6.10ms
LYNX_BENCH erlang/sets-union-result 5.80ms
LYNX_BENCH erlang/sets-union-commutative 19.23ms
LYNX_BENCH erlang/sets-union-empty 5.69ms
LYNX_BENCH native/sets-union-result 10.84ms
LYNX_BENCH native/sets-union-commutative 164.44ms
LYNX_BENCH native/sets-union-empty 5.48ms
```
