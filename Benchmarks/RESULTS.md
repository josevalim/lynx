# Benchmark results

Captured on 2026-09-06 using Lean 4.33.1 (release build) on macOS arm64.
Repository base: `9cae6af`, with the current working-tree changes.

Command, run from the repository root:

```sh
sh Benchmarks/run.sh 5
```

All five runs completed successfully. The current suites are Sum and Reverse.

## Median timings

Milliseconds, over five runs:

| Final proof | Lynx terms | Native Lean |
| --- | ---: | ---: |
| Sum integer-result contract | 223.45 | — |
| Sum append property | 785.18 | 13.13 |
| Reverse proper-list return contract | 86.98 | — |
| Reverse involution | 15.61 | 0.86 |
| Reverse append property | 58.66 | 5.30 |

These are final theorem-elaboration times, not execution times of the algorithms.
Supporting lemmas and imports are outside the timed sections. The Lynx contracts
and properties include executable expectations and successful return; native
lists encode properness in their type. A dash means there is no corresponding
benchmark, not zero cost. See [README.md](README.md) for measurement details.

Append reversal now uses a single accumulator invariant in each version, with
the induction performed inside the timed final proof. Shared append facts and
the accumulator invariant itself are elaborated outside the timed sections.

## Captured output

Timings are in milliseconds. Each consecutive group of eight lines is one run.

```text
LYNX_BENCH erlang/sum-contract 224.25ms
LYNX_BENCH erlang/sum-append 791.51ms
LYNX_BENCH native/sum-append 12.69ms
LYNX_BENCH erlang/reverse-contract 88.12ms
LYNX_BENCH erlang/reverse-involution 16.69ms
LYNX_BENCH erlang/reverse-append 58.66ms
LYNX_BENCH native/reverse-involution 0.90ms
LYNX_BENCH native/reverse-append 4.97ms
LYNX_BENCH erlang/sum-contract 219.15ms
LYNX_BENCH erlang/sum-append 779.57ms
LYNX_BENCH native/sum-append 12.54ms
LYNX_BENCH erlang/reverse-contract 85.90ms
LYNX_BENCH erlang/reverse-involution 14.91ms
LYNX_BENCH erlang/reverse-append 59.08ms
LYNX_BENCH native/reverse-involution 0.74ms
LYNX_BENCH native/reverse-append 4.93ms
LYNX_BENCH erlang/sum-contract 223.45ms
LYNX_BENCH erlang/sum-append 786.74ms
LYNX_BENCH native/sum-append 13.13ms
LYNX_BENCH erlang/reverse-contract 85.17ms
LYNX_BENCH erlang/reverse-involution 15.32ms
LYNX_BENCH erlang/reverse-append 57.81ms
LYNX_BENCH native/reverse-involution 0.86ms
LYNX_BENCH native/reverse-append 5.32ms
LYNX_BENCH erlang/sum-contract 222.29ms
LYNX_BENCH erlang/sum-append 777.97ms
LYNX_BENCH native/sum-append 13.17ms
LYNX_BENCH erlang/reverse-contract 86.98ms
LYNX_BENCH erlang/reverse-involution 15.61ms
LYNX_BENCH erlang/reverse-append 58.67ms
LYNX_BENCH native/reverse-involution 0.98ms
LYNX_BENCH native/reverse-append 5.63ms
LYNX_BENCH erlang/sum-contract 225.17ms
LYNX_BENCH erlang/sum-append 785.18ms
LYNX_BENCH native/sum-append 13.93ms
LYNX_BENCH erlang/reverse-contract 89.54ms
LYNX_BENCH erlang/reverse-involution 15.73ms
LYNX_BENCH erlang/reverse-append 57.06ms
LYNX_BENCH native/reverse-involution 0.82ms
LYNX_BENCH native/reverse-append 5.30ms
```
