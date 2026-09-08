# Benchmark results

Captured on 2026-09-08 with Lean 4.33.1 on macOS arm64 after consolidating
comparison and semantic equality in `Lynx/Term/Compare.lean`, with private map views.
Repository base: `4e3b9a5`, with the working-tree changes.

```sh
sh Benchmarks/run.sh 5
```

All 30 fresh Lean processes passed, with five runs of each translated/native
Sum, Reverse, and Sets file. All 70 timed declarations elaborated successfully.

Times below are median declaration-elaboration milliseconds, measured by
`#bench` after imports with `Elab.async false`. They exclude executable operation
runtime, process startup, imports, and supporting-library checking. The runner
checks source files directly, rather than importing cached target proofs.

| Target | Translated | Native |
| --- | ---: | ---: |
| Sum result contract | 252.04 | — |
| Sum append | 700.26 | 13.34 |
| Reverse return contract | 102.48 | — |
| Reverse involution | 17.48 | 0.76 |
| Reverse append | 53.89 | 5.20 |
| Sets union contract | 118.77 | 14.38 |
| Sets union commutativity | 61.97 | 168.78 |
| Sets union empty identity | 17.09 | 6.59 |

## Captured output

Each consecutive group of 14 lines is one run.

```text
LYNX_BENCH erlang/sum-contract 251.93ms
LYNX_BENCH erlang/sum-append 700.26ms
LYNX_BENCH native/sum-append 13.06ms
LYNX_BENCH erlang/reverse-contract 101.39ms
LYNX_BENCH erlang/reverse-involution 18.31ms
LYNX_BENCH erlang/reverse-append 53.12ms
LYNX_BENCH native/reverse-involution 0.74ms
LYNX_BENCH native/reverse-append 4.77ms
LYNX_BENCH erlang/sets-union-contract 119.84ms
LYNX_BENCH erlang/sets-union-commutative 63.67ms
LYNX_BENCH erlang/sets-union-empty 17.81ms
LYNX_BENCH native/sets-union-contract 14.38ms
LYNX_BENCH native/sets-union-commutative 168.78ms
LYNX_BENCH native/sets-union-empty 7.24ms
LYNX_BENCH erlang/sum-contract 255.44ms
LYNX_BENCH erlang/sum-append 716.41ms
LYNX_BENCH native/sum-append 13.73ms
LYNX_BENCH erlang/reverse-contract 104.64ms
LYNX_BENCH erlang/reverse-involution 17.35ms
LYNX_BENCH erlang/reverse-append 56.10ms
LYNX_BENCH native/reverse-involution 0.75ms
LYNX_BENCH native/reverse-append 5.56ms
LYNX_BENCH erlang/sets-union-contract 115.24ms
LYNX_BENCH erlang/sets-union-commutative 61.97ms
LYNX_BENCH erlang/sets-union-empty 18.43ms
LYNX_BENCH native/sets-union-contract 21.63ms
LYNX_BENCH native/sets-union-commutative 169.01ms
LYNX_BENCH native/sets-union-empty 6.45ms
LYNX_BENCH erlang/sum-contract 248.59ms
LYNX_BENCH erlang/sum-append 693.72ms
LYNX_BENCH native/sum-append 13.34ms
LYNX_BENCH erlang/reverse-contract 102.48ms
LYNX_BENCH erlang/reverse-involution 17.17ms
LYNX_BENCH erlang/reverse-append 53.12ms
LYNX_BENCH native/reverse-involution 0.80ms
LYNX_BENCH native/reverse-append 5.20ms
LYNX_BENCH erlang/sets-union-contract 130.06ms
LYNX_BENCH erlang/sets-union-commutative 61.21ms
LYNX_BENCH erlang/sets-union-empty 16.63ms
LYNX_BENCH native/sets-union-contract 13.29ms
LYNX_BENCH native/sets-union-commutative 167.78ms
LYNX_BENCH native/sets-union-empty 6.80ms
LYNX_BENCH erlang/sum-contract 252.04ms
LYNX_BENCH erlang/sum-append 696.51ms
LYNX_BENCH native/sum-append 12.60ms
LYNX_BENCH erlang/reverse-contract 100.29ms
LYNX_BENCH erlang/reverse-involution 17.48ms
LYNX_BENCH erlang/reverse-append 53.89ms
LYNX_BENCH native/reverse-involution 0.76ms
LYNX_BENCH native/reverse-append 5.04ms
LYNX_BENCH erlang/sets-union-contract 115.25ms
LYNX_BENCH erlang/sets-union-commutative 61.86ms
LYNX_BENCH erlang/sets-union-empty 17.09ms
LYNX_BENCH native/sets-union-contract 14.53ms
LYNX_BENCH native/sets-union-commutative 162.02ms
LYNX_BENCH native/sets-union-empty 6.43ms
LYNX_BENCH erlang/sum-contract 256.10ms
LYNX_BENCH erlang/sum-append 712.43ms
LYNX_BENCH native/sum-append 13.44ms
LYNX_BENCH erlang/reverse-contract 103.63ms
LYNX_BENCH erlang/reverse-involution 17.52ms
LYNX_BENCH erlang/reverse-append 56.15ms
LYNX_BENCH native/reverse-involution 0.82ms
LYNX_BENCH native/reverse-append 5.59ms
LYNX_BENCH erlang/sets-union-contract 118.77ms
LYNX_BENCH erlang/sets-union-commutative 63.92ms
LYNX_BENCH erlang/sets-union-empty 16.37ms
LYNX_BENCH native/sets-union-contract 13.77ms
LYNX_BENCH native/sets-union-commutative 169.15ms
LYNX_BENCH native/sets-union-empty 6.59ms
```
