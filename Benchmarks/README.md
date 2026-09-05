# Verification strategy benchmark

Run from the repository root:

```console
sh Benchmarks/run.sh 3 2>&1 | grep LYNX_BENCH
```

Each variant runs in a separate Lean process. The benchmark measures theorem
elaboration, including tactic execution, after imports have loaded. It compares
the current Lynx strategy, including its fixed generic `andalso` theorem, with
an analogous theorem over native `List Int`.

Native Lean is a useful lower bound, not an equivalent representation: it excludes
Elixir terms, exceptions, truthiness, and partial operations.

Run several times and compare medians. Separate processes prevent an earlier
theorem in one variant from warming a later variant's tactic state. Absolute
times still depend on the machine and Lean build cache.
