# Daxie

Daxie models Erlang terms and process effects in Dafny, with native IEEE
binary64 floats. It reproduces the integer-list sum and map-backed set union
verification experiments from `Lean/`.

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

- `Daxie/Term.dfy`: unbounded integers, native `fp64` floats, atoms, closures,
  PIDs, tuples, maps, nil, and cons cells, including improper lists. A subset
  type restricts float terms to finite values. Closures contain a whole-program
  function ID, arity, and captured terms.
- `Daxie/Arithmetic.dfy`: `add_2` uses integer addition or native binary64
  addition. Mixed operands convert the integer with nearest-even rounding
  using `fp64.FromReal`. Non-finite conversions and results return `badarith`.
  The integer-addition contract is verified and opaque to sum proofs.
- `Daxie/Compare.dfy`: numeric and exact comparison, plus eight comparison
  operators returning boolean atoms. Numeric order is
  `number < atom < function < pid < tuple < map < nil < cons`. Atoms compare lexicographically,
  tuples compare arity before elements, and cons cells compare heads before
  tails. Float comparisons use native operators; mixed comparisons first
  compare the integer against the float's truncation, then resolve fractional
  ties. The input integer is never rounded to a float. Exact order puts integers before floats
  and distinguishes the signs of zero, matching the existing Lean model.
  Closures compare IDs, then captures exactly; arity comes from the program's
  ID table. Maps compare effective size, all keys, then values. Keys always
  use exact comparison; values use the requested numeric or exact comparison.
- `Daxie/List.dfy` and `Daxie/Maps.dfy`: maps store `List<(Term, Term)>`.
  Lookup takes the first exactly matching key, put prepends a binding, and
  merge prepends the right operand's entries. Equality ignores entry order
  and shadowed bindings. Ordering uses a sorted, deduplicated view without
  changing storage. Integer/float keys and signed-zero keys remain distinct.
- `Daxie/Sum.dfy`: Term sum, integer-list expectation, and append.
  Invalid tails return `function_clause`; invalid elements return `badarith`
  after the recursive tail computation succeeds.
- `Benchmarks/NativeSum.dfy`: the same recursive shape using an inductive list
  of unbounded integers, without Term or Result wrappers.
- `Benchmarks/TermSets.dfy` and `Benchmarks/NativeSets.dfy`: right-biased map
  union, with a set defined by all effective values being empty lists.
  The native representation is `map<int, List<int>>`. Both representations
  allow non-set values, so the set invariant is meaningful.

### Anonymous functions and processes

`Daxie/Process.dfy` provides `apply_2`, `spawn_1`, `send_2`, and `self_0`.
Functions return `Result`, which carries values, errors, or requests for the
runner. `Bind` composes computations and propagates errors. Its deferred
`Then` node lets the runner maintain the continuation stack explicitly.

`Daxie/Runner.dfy` uses immutable state. Only the runner takes `Program`, whose
arity table and dispatcher cover all generated modules. Function bodies receive
their captures and arguments and emit requests; they do not thread `Program`
or `Runtime` through every call. `Tests/Processes.dfy` shows captured adders,
calls between generated bodies, recursive apply, and a spawned worker.

The root PID is 1; spawn allocates increasing PIDs and starts zero-arity
closures with empty mailboxes. Send appends to a live recipient's mailbox and
returns the message. Sending to an absent or finished PID succeeds without
delivery. A child error does not terminate its parent. This model supports
local PIDs; receive, registered names, links, and other exception classes are
not implemented.

A supplied sequence of PIDs chooses the next process at spawn/send boundaries.
An absent choice preserves the runnable order. Without a choice, the current
process continues until completion. Each interpreter step consumes fuel;
`Exhausted` is distinct from `Completed`, which requires every process to finish.
This is a deterministic model for exploring schedules, not an OS thread runner.

## Verification and tests

The sum contract proves every proper integer list returns an integer. Both
append theorems prove `sum(left ++ right) = sum(left) + sum(right)` for arbitrary
integer lists. `Tests/Correspondence.dfy` proves both implementations agree for
every encoded native list. Definitions and lemma bodies are verified without
axioms or admitted proofs.

The set proofs cover preservation of the set invariant, union commutativity,
and union with the empty map, using logical predicates on effective bindings.
Supporting lemmas establish lookup through merge and equality of such sets.
The runtime also verifies a captured adder for arbitrary integer arguments and
that delivery changes only matching mailboxes. General comparator order laws
and a full correspondence with Erlang process semantics are not proved.

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

`Tests/Maps.dfy` covers lookup, replacement, merge precedence, shadowing, nested
map and closure keys, map ordering, and signed-zero keys. `Tests/Processes.dfy`
covers closures, dispatch errors, scheduling, mailbox order, child failures,
and fuel exhaustion. These tests are compiled and executed too.

## Benchmarks

These measure **verification time**, not execution speed. The runner verifies
all project sources first, then launches a fresh Dafny process per suite with
one verification core. After a discarded warm-up per suite, it alternates suite
order and reports medians from the requested number of runs.

Only final sum and set lemmas are measured. Each time sums Dafny CSV correctness and
contract well-formedness batches; imports, parsing, process startup, and
supporting lemmas are excluded. The native return type already guarantees an
integer, so it has no separate return-contract proof. SMT resource counts are
recorded alongside durations.

Each run creates a fresh log directory containing CSV batches, verifier output,
`samples.tsv`, `summary.tsv`, and the toolchain version. See
[Benchmarks/RESULTS.md](Benchmarks/RESULTS.md) for captured results. These Dafny
SMT batch timings are not directly comparable to Lean theorem-elaboration times.
