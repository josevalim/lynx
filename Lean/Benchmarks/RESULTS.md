# Benchmark results

Captured on 2026-09-30 with Lean 4.33.1 on macOS arm64.

```sh
sh Benchmarks/run.sh 5
```

All 30 fresh Lean processes and 70 timed declarations passed.
Times are median proof-elaboration milliseconds, not executable runtime.
Measurements exclude imports and supporting lemmas; later proofs in each file
may reuse earlier results and cached summaries.

| Target | Translated (ms) | Native (ms) |
| --- | ---: | ---: |
| Sum result contract | 145.80 | — |
| Sum append | 626.15 | 12.63 |
| Reverse return contract | 11.52 | — |
| Reverse involution | 8.86 | 0.72 |
| Reverse append | 75.54 | 5.01 |
| Sets union contract | 75.49 | 13.59 |
| Sets union commutativity | 50.85 | 161.13 |
| Sets union empty identity | 15.59 | 6.31 |

## Captured output

Each consecutive group of 14 lines is one run.

```text
LYNX_BENCH erlang/sum-contract 142.46ms
LYNX_BENCH erlang/sum-append 608.27ms
LYNX_BENCH native/sum-append 12.19ms
LYNX_BENCH erlang/reverse-contract 12.14ms
LYNX_BENCH erlang/reverse-involution 9.17ms
LYNX_BENCH erlang/reverse-append 75.54ms
LYNX_BENCH native/reverse-involution 0.81ms
LYNX_BENCH native/reverse-append 4.92ms
LYNX_BENCH erlang/sets-union-contract 74.88ms
LYNX_BENCH erlang/sets-union-commutative 48.78ms
LYNX_BENCH erlang/sets-union-empty 15.26ms
LYNX_BENCH native/sets-union-contract 13.75ms
LYNX_BENCH native/sets-union-commutative 158.84ms
LYNX_BENCH native/sets-union-empty 7.05ms
LYNX_BENCH erlang/sum-contract 139.64ms
LYNX_BENCH erlang/sum-append 615.51ms
LYNX_BENCH native/sum-append 12.57ms
LYNX_BENCH erlang/reverse-contract 13.08ms
LYNX_BENCH erlang/reverse-involution 9.39ms
LYNX_BENCH erlang/reverse-append 88.44ms
LYNX_BENCH native/reverse-involution 0.70ms
LYNX_BENCH native/reverse-append 5.01ms
LYNX_BENCH erlang/sets-union-contract 81.29ms
LYNX_BENCH erlang/sets-union-commutative 54.48ms
LYNX_BENCH erlang/sets-union-empty 17.66ms
LYNX_BENCH native/sets-union-contract 13.59ms
LYNX_BENCH native/sets-union-commutative 161.13ms
LYNX_BENCH native/sets-union-empty 6.26ms
LYNX_BENCH erlang/sum-contract 152.54ms
LYNX_BENCH erlang/sum-append 631.17ms
LYNX_BENCH native/sum-append 13.13ms
LYNX_BENCH erlang/reverse-contract 11.36ms
LYNX_BENCH erlang/reverse-involution 8.77ms
LYNX_BENCH erlang/reverse-append 72.45ms
LYNX_BENCH native/reverse-involution 0.72ms
LYNX_BENCH native/reverse-append 4.79ms
LYNX_BENCH erlang/sets-union-contract 80.72ms
LYNX_BENCH erlang/sets-union-commutative 51.35ms
LYNX_BENCH erlang/sets-union-empty 15.83ms
LYNX_BENCH native/sets-union-contract 13.79ms
LYNX_BENCH native/sets-union-commutative 161.55ms
LYNX_BENCH native/sets-union-empty 6.49ms
LYNX_BENCH erlang/sum-contract 153.00ms
LYNX_BENCH erlang/sum-append 635.46ms
LYNX_BENCH native/sum-append 13.45ms
LYNX_BENCH erlang/reverse-contract 11.41ms
LYNX_BENCH erlang/reverse-involution 8.78ms
LYNX_BENCH erlang/reverse-append 73.07ms
LYNX_BENCH native/reverse-involution 0.71ms
LYNX_BENCH native/reverse-append 5.56ms
LYNX_BENCH erlang/sets-union-contract 75.40ms
LYNX_BENCH erlang/sets-union-commutative 50.85ms
LYNX_BENCH erlang/sets-union-empty 15.51ms
LYNX_BENCH native/sets-union-contract 13.28ms
LYNX_BENCH native/sets-union-commutative 161.06ms
LYNX_BENCH native/sets-union-empty 6.31ms
LYNX_BENCH erlang/sum-contract 145.80ms
LYNX_BENCH erlang/sum-append 626.15ms
LYNX_BENCH native/sum-append 12.63ms
LYNX_BENCH erlang/reverse-contract 11.52ms
LYNX_BENCH erlang/reverse-involution 8.86ms
LYNX_BENCH erlang/reverse-append 75.73ms
LYNX_BENCH native/reverse-involution 0.80ms
LYNX_BENCH native/reverse-append 5.14ms
LYNX_BENCH erlang/sets-union-contract 75.49ms
LYNX_BENCH erlang/sets-union-commutative 49.24ms
LYNX_BENCH erlang/sets-union-empty 15.59ms
LYNX_BENCH native/sets-union-contract 13.13ms
LYNX_BENCH native/sets-union-commutative 161.91ms
LYNX_BENCH native/sets-union-empty 6.10ms
```
