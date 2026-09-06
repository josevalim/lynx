# Benchmark results

Captured on 2026-09-06 using Lean 4.33.1 (release build, commit
`4d4d5e4`) on macOS arm64.

Command, run from the repository root:

```sh
sh Benchmarks/run.sh 5
```

All five runs completed successfully. The current suites are Sum and Reverse.

## Median timings

Milliseconds, over five runs:

| Final proof | Lynx terms | Native Lean |
| --- | ---: | ---: |
| Sum integer-result contract | 222.47 | — |
| Sum append property | 805.91 | 13.02 |
| Reverse proper-list return contract | 86.51 | — |
| Reverse involution | 15.88 | 1.34 |
| Native reverse exact result | — | 1.75 |

These are final theorem-elaboration times, not execution times of the algorithms.
Supporting lemmas and imports are outside the timed sections. The Lynx contracts
and properties include executable expectations and successful return; native
lists encode properness in their type. A dash means there is no corresponding
benchmark, not zero cost. See [README.md](README.md) for measurement details.

## Captured output

The original output below has been converted to milliseconds, matching the
current reporting format. Each consecutive group of seven lines is one run.

```text
LYNX_BENCH erlang/sum-contract 219.32ms
LYNX_BENCH erlang/sum-append 791.50ms
LYNX_BENCH native/sum-append 12.80ms
LYNX_BENCH erlang/reverse-contract 87.54ms
LYNX_BENCH erlang/reverse-involution 15.99ms
LYNX_BENCH native/reverse-correctness 1.47ms
LYNX_BENCH native/reverse-involution 1.49ms
LYNX_BENCH erlang/sum-contract 225.95ms
LYNX_BENCH erlang/sum-append 833.61ms
LYNX_BENCH native/sum-append 13.02ms
LYNX_BENCH erlang/reverse-contract 86.44ms
LYNX_BENCH erlang/reverse-involution 15.30ms
LYNX_BENCH native/reverse-correctness 1.75ms
LYNX_BENCH native/reverse-involution 1.23ms
LYNX_BENCH erlang/sum-contract 231.91ms
LYNX_BENCH erlang/sum-append 821.12ms
LYNX_BENCH native/sum-append 14.07ms
LYNX_BENCH erlang/reverse-contract 86.51ms
LYNX_BENCH erlang/reverse-involution 15.50ms
LYNX_BENCH native/reverse-correctness 1.97ms
LYNX_BENCH native/reverse-involution 1.40ms
LYNX_BENCH erlang/sum-contract 222.47ms
LYNX_BENCH erlang/sum-append 802.94ms
LYNX_BENCH native/sum-append 13.42ms
LYNX_BENCH erlang/reverse-contract 84.83ms
LYNX_BENCH erlang/reverse-involution 15.88ms
LYNX_BENCH native/reverse-correctness 1.80ms
LYNX_BENCH native/reverse-involution 1.34ms
LYNX_BENCH erlang/sum-contract 220.64ms
LYNX_BENCH erlang/sum-append 805.91ms
LYNX_BENCH native/sum-append 12.87ms
LYNX_BENCH erlang/reverse-contract 91.42ms
LYNX_BENCH erlang/reverse-involution 15.91ms
LYNX_BENCH native/reverse-correctness 1.33ms
LYNX_BENCH native/reverse-involution 1.19ms
```
