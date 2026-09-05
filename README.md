# Lynx

An experimental Elixir-to-Lean translation and verification project.

## Elixir syntax

Contracts and properties are written as ordinary Elixir expressions immediately
before a function definition:

```elixir
expects is_list(list) and Enum.all?(list, &is_number/1)
ensures (result -> is_number(result))
property sum(l) + sum(r) == sum(l ++ r)
def sum(list)
```

- `expects` restricts the inputs for which Lynx verifies the function.
- `ensures` states a guarantee about a successful return. The name to the left
  of `->` is a local binding for the returned value, not a reserved name.
- `property` states an additional expression that Lynx must prove. It can call
  the function directly and does not have an implicit result binding.

All three clauses contain single expressions; they do not introduce `do` blocks.

## Lean verification

The verifier starts from translated Lean expressions. The Elixir frontend is
not implemented yet. Import `Lynx`; executable definitions are discovered
automatically from their `Outcome` return type:

```lean
import Lynx
open Lynx Lynx.Modules

def increment (arg : Term) : Outcome Term :=
  Erlang.add arg (.integer 1)

def expects (arg : Term) : Outcome Term :=
  Erlang.is_integer arg

def ensures (_arg result : Term) : Outcome Term :=
  Erlang.is_integer result

example : Satisfies increment expects ensures := by
  lynx_verify
```

`Accepted` means exactly a normal return of the atom `true`. `Satisfies`
requires both a nonempty accepted domain and a normal function result with an
accepted guarantee for every accepted input. Its argument container is implicit: use `Term`, a Lean tuple, or a
generated structure. `Property expects expression` verifies an expression under
an explicit domain. Elixir lists remain `Term.nil` and `Term.cons`, including
improper lists; Lean tuples and structures only package function arguments.

`SourceLabel` stores a source file and line separately. Use
`WithSourceLabel { file := "sum.ex", line := 4 } proposition` to attach it to
any Lean proposition. `lynx_vcgen` names the resulting goal `sum.ex:4`.
`EnsuresClauses function expects [(source, ensures), ...]`
groups the translated Elixir `ensures` clauses, one shared coverage condition,
and one named behavioral obligation per clause. Each refers to the same actual
function outcome. The temporary aliases `accepts` and `SatisfiesUnary`
remain available for existing translations.

For interactive proofs, replace `lynx_verify` with:

```lean
  lynx_vcgen
  all_goals lynx_solve
```

`lynx_vcgen` exposes named coverage and normal-return obligations without
solving them; it still runs the early empty-domain diagnostic. `lynx_solve` follows calls into executable definitions and
builds a simplification context once per verification condition. It simplifies
expectations before the rest of each branch, discarding rejected inputs before
exploring their results. Induction follows the structurally recursive argument;
independent inputs can each be inducted. Matches drive constructor case splits,
and shared monadic computations are inspected once, without eagerly expanding
all their continuations. Lean's arithmetic and congruence solvers close leaves.

For relational properties, the solver can conjecture normal-return summaries
for unary recursive functions. It discovers candidate domains inside the
expectation and a candidate result constructor in the implementation, then
proves each summary in a fresh context before using it. It neither assumes a
callee's expectation nor reuses separately proved application contracts.
There are no predefined integer-list/domain lemmas or required semantic
theorem module. Executable operation definitions and Lean's ordinary
simplification rules remain the basis of verification.

The search is bounded and incomplete. Unsupported operations, recursion needing
a stronger invariant, and more general result summaries may leave goals for
ordinary Lean tactics. Summary inference currently handles unary functions
with a uniform candidate result constructor; it is not general invariant
inference. The tactic has a small fixed set of generic, proved shortcuts, but
translated definitions need no annotation or registration mechanism.
`set_option trace.lynx true` shows structural proof-search steps. The module
documentation in [Lynx/Tactic.lean](Lynx/Tactic.lean) describes the complete
algorithm and trust boundary.

Coverage is part of `Satisfies` and `Property`, not a warning-only check. If
automatic coverage is inconclusive, verification reports that `expects` may be
empty or use a shape the tactic does not yet support. Lean integrations can use
`lynx_vcgen` to prove the remaining coverage condition directly.

## Implementation

Build the public library with:

```console
lake build
```

Elaborate and kernel-check the integration-test examples with:

```console
lake test
```

`LynxTest/Integration` contains end-to-end translated examples. Focused tactic
tests live under `LynxTest/Tactic` and cover contracts, source-labelled VCs,
distinct recursion shapes, representative failures, and coverage diagnostics.
Positive proofs are checked by Lean's kernel; a proof audit rejects dependencies
on `sorryAx` or nonstandard axioms.
