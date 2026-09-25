Start with the README.md to understand the general project scope.
Do not change the README.md unless asked to do so.

## Lean

All package paths below are relative to `Lean/`.

Use Lean's `module` system with explicit `public` declarations and deliberate
`public import` re-exports. Update `LynxTest/PublicApi.lean` for exported API
changes. Its snapshot must check actual public declarations without excluding
modules by name. Keep other implementation details private and use
`import all` where needed.

The Erlang Term definition and its general properties are defined
in Lynx/Term.lean and within the Lynx/Term/ directory.

The implementation of Erlang NIFs goes to Lynx/Modules/.
Functions follow their Erlang name with the arity followed
by underscore, such as `is_integer_1`. The translator may also
emit generated, program-local helper functions. Functions that
are pure from Elixir's point of view (they don't spawn messages
or use pdict, albeit they can raise) should be tagged with #lynx_pure.

Prefer unfolding over lemmas that merely restate definitions.
Keep lemmas needed for useful simplification or mathematical properties,
use `lynx_opaque` only when tests or benchmarks justify specification-based
proof search.

Integration tests go in LynxTest/Integration and they all
have the same shape: they have a version of the Elixir module
at the top and their manual translation in LEAN, including the
implementation, ensures, and expects. Preferrably verifications
are then done with the `lynx_verify` tactic instead of custom
theorems.

Whenever a new integration example is added, you must also add
a Benchmarks/Native equivalent example, using the same data types
but without the Term wrapping, so we can compare them. Add the
relevant #bench annotations to both native and integration.
Read Benchmarks/README.md for context around benchmarks.
Update RESULTS.md on new benchmarks but only change the minimum
amount of text necessary. The overall goal is to facilitate proofs,
which is more valuable than proof performance. Runtime performance
itself is not an important metric (the code is not meant to run at
speed).

## Benchmarks

When changing `Result`, `Outcome`, or the runtime, run the existing verification
benchmarks even if their examples do not use the new operation. New constructors
can add branches to `lynx_verify` proofs. Compare medians from repeated runs
against the preceding commit on the same machine, with each revision built from
its own source. The measured sections exclude imports and supporting lemmas;
also run `lake test` to check those proofs.

Keep the tactic's search focused on useful proof states. Simplify or close
impossible branches immediately after splitting a computation; do not spend
another search round on an outcome contradicted by a local equation. Preserve
shared binds until their result is needed, and retain input variables needed
for induction. Normalize expectation constraints before implementation results,
and avoid repeatedly simplifying quantified induction hypotheses.

Reuse a simplification context within a search, install known declarations
directly instead of elaborating the same `simp_all` syntax in every goal, and
try definitional evaluation before building a context for coverage. Use proved
specifications and `lynx_opaque` for expensive abstractions when benchmarks
justify the boundary. Check that new simp rules or proof search shortcuts help
representative contracts and properties, including `sum-append`; a faster
single proof can still slow the rest of the suite.
