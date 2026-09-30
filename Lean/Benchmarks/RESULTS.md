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
| Sum result contract | 132.37 | — |
| Sum append | 1185.02 | 12.53 |
| Reverse return contract | 11.18 | — |
| Reverse involution | 8.56 | 0.70 |
| Reverse append | 219.53 | 5.08 |
| Sets union contract | 218.81 | 13.05 |
| Sets union commutativity | 191.16 | 155.35 |
| Sets union empty identity | 15.46 | 5.88 |

## Captured output

Each consecutive group of 14 lines is one run.

```text
LYNX_BENCH erlang/sum-contract 132.37ms
LYNX_BENCH erlang/sum-append 1185.02ms
LYNX_BENCH native/sum-append 12.98ms
LYNX_BENCH erlang/reverse-contract 11.04ms
LYNX_BENCH erlang/reverse-involution 8.56ms
LYNX_BENCH erlang/reverse-append 220.93ms
LYNX_BENCH native/reverse-involution 0.70ms
LYNX_BENCH native/reverse-append 5.09ms
LYNX_BENCH erlang/sets-union-contract 218.10ms
LYNX_BENCH erlang/sets-union-commutative 192.83ms
LYNX_BENCH erlang/sets-union-empty 15.36ms
LYNX_BENCH native/sets-union-contract 13.17ms
LYNX_BENCH native/sets-union-commutative 154.86ms
LYNX_BENCH native/sets-union-empty 5.88ms
LYNX_BENCH erlang/sum-contract 129.28ms
LYNX_BENCH erlang/sum-append 1177.40ms
LYNX_BENCH native/sum-append 12.53ms
LYNX_BENCH erlang/reverse-contract 11.27ms
LYNX_BENCH erlang/reverse-involution 8.53ms
LYNX_BENCH erlang/reverse-append 215.34ms
LYNX_BENCH native/reverse-involution 0.72ms
LYNX_BENCH native/reverse-append 4.76ms
LYNX_BENCH erlang/sets-union-contract 218.37ms
LYNX_BENCH erlang/sets-union-commutative 187.70ms
LYNX_BENCH erlang/sets-union-empty 15.16ms
LYNX_BENCH native/sets-union-contract 13.10ms
LYNX_BENCH native/sets-union-commutative 155.83ms
LYNX_BENCH native/sets-union-empty 5.85ms
LYNX_BENCH erlang/sum-contract 132.88ms
LYNX_BENCH erlang/sum-append 1193.54ms
LYNX_BENCH native/sum-append 12.03ms
LYNX_BENCH erlang/reverse-contract 12.22ms
LYNX_BENCH erlang/reverse-involution 9.63ms
LYNX_BENCH erlang/reverse-append 219.53ms
LYNX_BENCH native/reverse-involution 0.71ms
LYNX_BENCH native/reverse-append 4.79ms
LYNX_BENCH erlang/sets-union-contract 218.81ms
LYNX_BENCH erlang/sets-union-commutative 190.40ms
LYNX_BENCH erlang/sets-union-empty 15.46ms
LYNX_BENCH native/sets-union-contract 12.68ms
LYNX_BENCH native/sets-union-commutative 155.35ms
LYNX_BENCH native/sets-union-empty 5.88ms
LYNX_BENCH erlang/sum-contract 131.17ms
LYNX_BENCH erlang/sum-append 1191.34ms
LYNX_BENCH native/sum-append 12.89ms
LYNX_BENCH erlang/reverse-contract 11.18ms
LYNX_BENCH erlang/reverse-involution 8.62ms
LYNX_BENCH erlang/reverse-append 221.74ms
LYNX_BENCH native/reverse-involution 0.70ms
LYNX_BENCH native/reverse-append 5.08ms
LYNX_BENCH erlang/sets-union-contract 222.35ms
LYNX_BENCH erlang/sets-union-commutative 191.16ms
LYNX_BENCH erlang/sets-union-empty 15.78ms
LYNX_BENCH native/sets-union-contract 12.77ms
LYNX_BENCH native/sets-union-commutative 158.84ms
LYNX_BENCH native/sets-union-empty 6.28ms
LYNX_BENCH erlang/sum-contract 134.31ms
LYNX_BENCH erlang/sum-append 1180.11ms
LYNX_BENCH native/sum-append 12.34ms
LYNX_BENCH erlang/reverse-contract 10.88ms
LYNX_BENCH erlang/reverse-involution 8.52ms
LYNX_BENCH erlang/reverse-append 215.02ms
LYNX_BENCH native/reverse-involution 0.69ms
LYNX_BENCH native/reverse-append 5.71ms
LYNX_BENCH erlang/sets-union-contract 220.63ms
LYNX_BENCH erlang/sets-union-commutative 191.20ms
LYNX_BENCH erlang/sets-union-empty 15.70ms
LYNX_BENCH native/sets-union-contract 13.05ms
LYNX_BENCH native/sets-union-commutative 154.51ms
LYNX_BENCH native/sets-union-empty 5.84ms
```
