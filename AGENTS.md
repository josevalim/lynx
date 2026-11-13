Start with the README.md to understand the general project scope.
Do not change the README.md unless asked to do so.

See `lib/lynx.ex` for general information on writing proofs.

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

### Concurrency

Processes are modeled by the labelled transition system in `Lynx/Concurrent.lean`
(`Config`, `Step`, `State.request`), and concurrent laws are proven by evaluating
`Lynx.Concurrent.check` (`Lynx/Concurrent/Reduction.lean`), whose soundness rests
on footprints (`Lynx/Concurrent/Footprint.lean`). Soundness with what OTP does is
non-negotiable, so a new process BIF, or a change to one, goes through every layer:

1. Model OTP from its source (`../otp`), not its documentation, including the
   corner cases (dead targets, self-targets, exit signals racing the request,
   `false` replies). Each reply must be one OTP can give, and every reply OTP can
   give must be reachable in some run.
2. Express the BIF in `Lynx/Modules/Erlang/erlang/Process.lean` as a `Result`
   built from existing requests where possible. A new kind of request extends
   `Request` (`Lynx/Term/DataTypes.lean`) and is answered by `State.request`.
   Keep signals between two processes in order, and put anything that reaches
   another process in transit (`State.emit`) rather than changing its record.
   Definitions that `check` evaluates use the list functions of
   `Lynx/Concurrent/Kernel.lean` rather than core's, as the kernel evaluates them
   much faster; proofs rewrite them back with their `_eq` lemmas.
3. Give the request a footprint in `requestFootprint`: what it observes and
   what it changes. A footprint that observes too little is unsound; one that
   observes too much only costs exploration. Extend `request_matches` and the
   commuting proofs, and `Task.local` only for steps that touch nothing but the
   process's own record. Termination (`Concurrent/Termination.lean`), traces
   (`Concurrent/Trace.lean`) and the runner (`Lynx/Term/Runner.lean`) must cover
   it too.
4. Look for steps that do nothing now and never will. For example, a `DOWN`
   in transit after its monitor was removed by `demonitor`, a message sent to an
   alias that was removed by `unalias`, or a message or exit signal to a process
   that has exited and can never be live again (`State.settled`). `check` takes such
   steps alone (`Config.forced`), so it never explores their interleavings with other
   steps. If the new BIF creates steps like these, recognize them from the configuration
   in `Envelope.inert`, or in a new case of `ForcedStep`. Then prove the obligations of
   `forced_first`: the step stays enabled, every other step either commutes with it or
   absorbs it, and the step stays forced.
   Not every such signal qualifies: a link or monitor signal to a process that has
   exited is not inert, because its bounce answers with an exit or a `DOWN`.
5. Register the BIF's purity in `@runtime_purity` (`lib/lynx/translation.ex`) and
   regenerate `Lean/modules.json` if its signature changed.
6. Test it in `LynxTest/Modules/Signals.lean` with kernel-checked closed programs
   for each OTP behavior, including races where the order of steps changes the
   reply, and update `LynxTest/PublicApi.lean`.
7. Before trusting a change to footprints or to how `check` explores, audit it
   executably: over every configuration reachable from closed programs that use
   the BIF, check that steps reported as commuting reach the same configuration
   in either order, and that the steps `check` takes alone lose no terminal
   configuration. Audits only cover the races the programs exercise, so write
   programs for each race (for example, a timer whose destination dies).
8. Measure the concurrent examples (`examples/concurrency`, `examples/elixir/task.exs`):
   explored configurations and kernel time, before and after.

### Examples

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

Run examples with `LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/<name>.exs` to
measure verification without cached results. Run `lake test` from `Lean/` to
check runtime proofs and axiom audits.

**Proof performance is more important than executable runtime performance.**
This priority concerns Lean's implementation and proof infrastructure; integration examples may take time to verify.

**DO NOT ADD CO-AUTHORED TO ANY OF THE COMMITS. Use ASSISTED-BY attribution instead.**
