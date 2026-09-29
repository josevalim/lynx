# Daxie

Daxie implements the integer-list sum verification experiment from `Lean/` in
Dafny, with native IEEE binary64 floats.

## Toolchain and commands

Use the ARM64 Dafny nightly dated 2026-09-28,
`4.11.1+5f717bf447b19d38cad1b69b1bf9a9f102feccfb`, and the .NET 8 SDK.
The shell runners prefer `$HOME/.dafny/bin/dafny` when present and otherwise
use `dafny` on PATH. `DAFNY` and `DOTNET` can override the executable paths.
The installed nightly is `/Users/jose/.dafny/bin/dafny`; .NET is on PATH.

```console
sh Dafny/Tests/run.sh
sh Dafny/Benchmarks/run.sh 5
```

For verification alone:

```console
/Users/jose/.dafny/bin/dafny verify Dafny/dfyconfig.toml
```

There are no third-party package dependencies. The test runner verifies every
Dafny file, generates C# with the bundled Dafny runtime and a minimal .NET
project, compiles it with the SDK, and runs the tests. The generated project has
no package references; restore uses only an empty local package source.

Every test run deletes `.build/` and regenerates its C# source and assemblies
from scratch. Generated code, SDK state, and build artifacts live in ignored
`.build/`; benchmark logs live in ignored `.benchmarks/`. Neither directory is
needed in a checkout. No shell configuration changes are needed.

## Model

- `Daxie/Term.dfy`: unbounded integers, native `fp64` floats, atoms, tuples,
  nil, and cons cells, including improper lists. A subset type restricts float
  terms to finite values. `Result` carries a returned term or error reason.
- `Daxie/Arithmetic.dfy`: `add_2` uses integer addition or native binary64
  addition. Mixed operands convert the integer with nearest-even rounding
  using `fp64.FromReal`. Non-finite conversions and results return `badarith`.
  The integer-addition contract is verified and opaque to sum proofs.
- `Daxie/Compare.dfy`: numeric and exact comparison, plus eight comparison
  operators returning boolean atoms. Numeric order is
  `number < atom < tuple < nil < cons`. Atoms compare lexicographically,
  tuples compare arity before elements, and cons cells compare heads before
  tails. Float comparisons use native operators; mixed comparisons first
  compare the integer against the float's truncation, then resolve fractional
  ties. The input integer is never rounded to a float. Exact order puts integers before floats
  and distinguishes the signs of zero, matching the existing Lean model.
- `Daxie/Sum.dfy`: Term sum, integer-list expectation, and append.
  Invalid tails return `function_clause`; invalid elements return `badarith`
  after the recursive tail computation succeeds.
- `Benchmarks/NativeSum.dfy`: the same recursive shape using an inductive list
  of unbounded integers, without Term or Result wrappers.

Term and Result dispatch uses pattern matching. This pure subset does not
model processes or exceptions other than errors.

## Verification and tests

The sum contract proves every proper integer list returns an integer. Both
append theorems prove `sum(left ++ right) = sum(left) + sum(right)` for arbitrary
integer lists. `Tests/Correspondence.dfy` proves both implementations agree for
every encoded native list. Definitions and lemma bodies are verified without
axioms or admitted proofs.

`Tests/Semantics.dfy` contains executable regressions for comparisons, nested
terms, invalid arguments, improper lists, rounding, signed zero, subnormals,
and non-finite result rejection. Result contents are compared explicitly:
the nightly does not support compiled structural equality of datatypes
containing `fp64`.

The nightly C# runtime also throws when converting subnormal floats to `real`.
The mixed comparator avoids this conversion and supports subnormal values.

All test logic lives in Dafny. The numeric edge cases cover both operand orders,
integer conversion ties, the binary64 overflow threshold, exact mixed ordering,
and signed zero. These are executable checks, separate from the universal sum
proofs. C# is generated only as the execution backend.

## Benchmarks

These measure **verification time**, not execution speed. The runner verifies
all project sources first, then launches a fresh Dafny process per suite with
one verification core. After a discarded warm-up per suite, it alternates suite
order and reports medians from the requested number of runs.

Only final sum lemmas are measured. Each time sums Dafny CSV correctness and
contract well-formedness batches; imports, parsing, process startup, and
supporting lemmas are excluded. The native return type already guarantees an
integer, so it has no separate return-contract proof. SMT resource counts are
recorded alongside durations.

Each run creates a fresh log directory containing CSV batches, verifier output,
`samples.tsv`, `summary.tsv`, and the toolchain version. See
[Benchmarks/RESULTS.md](Benchmarks/RESULTS.md) for captured results. These Dafny
SMT batch timings are not directly comparable to Lean theorem-elaboration times.
