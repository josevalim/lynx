Start with the README.md to understand the general project scope.
Do not change the README.md unless asked to do so.

## Translation

The translation code is done by `lib/lynx/translation.ex` and `src/lynx_core_to_leanj.erl`.

When changing the translator or Lean syntax decoder, regenerate the existing
translation fixtures from the repository root as appropriate:

    mix run test/fixtures/translations/regenerate.exs json
    mix run test/fixtures/translations/regenerate.exs lean

If both change, regenerate JSON first, then Lean.

Unit test relevant Core-to-JSON translation details directly in `test/lynx/core_to_leanj_test.exs`,
The integration test should focus exclusively on the translation fixtures which
validate Erlang code against the generated JSON and Lean sources (plus elaboration).
Test Lean runtime features and their properties in Lean's `LynxTest/` suite,
including kernel-checked proofs and axiom audits.

When matching JSON values in tests, prefer pattern matching on the shape as a
whole rather than multiple assertions on individual fields.

## Lean

All package paths below are relative to `Lean/`.

The Erlang Term definition and its general properties are defined
in `Lynx/Term.lean` and within the `Lynx/Term/` directory.
`Lynx.Term` re-exports `Term.induct` for structural proofs over nested term fields.
Keep `Lynx.Term` focused on runtime definitions and foundational comparison,
monad, and purity facts. Put laws about Erlang operations in the corresponding
`Erlang.*` module.

Public executable definitions in `Erlang.*` must correspond to existing Erlang
functions. Put translation and runtime helpers in `Lynx.*`, such as `Lynx.Term`,
instead of adding helper functions to `Erlang.maps` or other Erlang modules.

Use Lean's `module` system with explicit `public` declarations and deliberate
`public import` re-exports. Update `LynxTest/PublicApi.lean` for exported API
changes. Its snapshot must check actual public declarations without excluding
modules by name. Keep implementation details private.

Client code, translated programs, integration proofs, and benchmarks must use
ordinary imports of the public Lynx and Erlang entry points. Do not use
`import all` on runtime library modules to bypass their public proof interface.
If a proof needs to unfold a public operation, deliberately expose its body with
`@[expose]` or provide a useful public lemma. Keep private helpers private.
`import all` is reserved for intentional dependencies within the implementation
and for proof audits that inspect private declarations in test modules.

Functions that neither inspect nor change the environment and perform no process
effects return `Except Exception Term`. They may still raise exceptions. Other
computations embed their calls with `Result.ofExcept`. Functions that may
additionally not return, such as cutoffs and partial fixed points, also return
`Except`: not returning raises `Exception.exhausted`, the least element of the
order used by `partial_fixpoint`. It is not an Erlang exception. Every handler,
guard, and the scheduler must propagate it without catching it.

Proofs must not introduce untrusted axioms or `sorry`

### Proofs and examples

Do not add new examples unless explicitly requested. Existing examples may be
run as regression checks.

Integration examples go in `examples/` and use `Lynx.Case` to verify laws.
Keep the implementation separate from its properties. Use `requires:` for input
assumptions and `expects:` for the expression to prove, with a `~LEAN` proof.

When investigating a bug, state the intended general property and let verification
fail on the buggy implementation. Do not replace it with a passing law asserting
the incorrect behavior, or restrict its assumptions to exclude the bug. Concrete
counterexamples belong in ordinary tests. Document intentional failing properties
and the OTP version checked; do not use `sorry` or axioms to make them pass.

Simplify or close impossible branches promptly after a case split. Preserve input
variables needed for induction and avoid unnecessarily expanding shared binds.
When adding simp rules or changing public proof interfaces, check representative
guarantees and properties. Improving one proof can slow another.

Run examples with `LYNX_PROFILE=1 LYNX_CACHE=0 mix run examples/<name>.exs` to
measure verification without cached results. Run `lake test` from `Lean/` to
check runtime proofs and axiom audits.

**Proof performance is more important than executable runtime performance.**
This priority concerns Lean's implementation and proof infrastructure; integration
examples may take time to verify.
