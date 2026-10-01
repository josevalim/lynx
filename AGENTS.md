Start with the README.md to understand the general project scope.
Do not change the README.md unless asked to do so.

## Lean

When changing the translator or Lean syntax decoder, regenerate the existing
translation fixtures from the repository root as appropriate:
`mix run test/fixtures/translations/regenerate.exs json` for JSON changes and
`mix run test/fixtures/translations/regenerate.exs lean` for rendered Lean changes.
If both change, regenerate JSON first, then Lean.

All package paths below are relative to `Lean/`.

The Erlang Term definition and its general properties are defined
in `Lynx/Term.lean` and within the `Lynx/Term/` directory.
`Lynx.Term` re-exports `Term.induct` for structural proofs over nested term fields.
Keep `Lynx.Term` focused on runtime definitions and foundational comparison,
monad, and purity facts. Put laws about Erlang operations in the corresponding
`Erlang.*` module.

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
effects should be tagged with `#lynx_pure`. They may still raise exceptions.
`Lynx/Pure.lean` generates ordinary kernel-checked `<name>_pure` lemmas,
registered for simplification, without a contract verification tactic.

Proofs must not introduce untrusted axioms or `sorry`

### Proofs and integration examples

Integration tests go in `LynxTest/Integration`. Start each example with an Elixir
module comment containing only the implementation, followed by its faithful
Erlang/Term translation. Keep the implementation separate from its properties.
For each final theorem, include a separate source comment such as:

```lean
/- law sum_append(l, r),
     requires: is_integer_list(l) and is_integer_list(r),
     expects: sum(l) + sum(r) == sum(l ++ r) -/
```

Use `requires:` for input assumptions and `expects:` for an expression to prove
or a return guarantee written as `(result -> ...)`, as applicable. These are
illustrative source comments, not an implemented law DSL. Follow them with the
translated computation or predicate and an explicit Lean theorem and handwritten
proof. A successful Boolean property is an equation to `Result.ok Term.true`.
A return guarantee establishes a successful result and the stated predicate.

Simplify or close impossible branches promptly after a case split. Preserve input
variables needed for induction and avoid unnecessarily expanding shared binds.
When adding simp rules or changing public proof interfaces, check representative
guarantees and properties. Improving one proof can slow another.

Whenever a new integration example is added, also add a `Benchmarks/Native`
equivalent using corresponding native data types without Term wrapping. Use the
same implementation-comment and separate law-comment layout. Add relevant
`#bench` annotations to native and integration theorems.

## Benchmarks

Read `Benchmarks/README.md` for the benchmark execution and measurement workflow.
Update `Benchmarks/RESULTS.md` on new benchmarks, changing only the minimum text
necessary. Compare medians from repeated runs against the preceding commit on the
same machine, with each revision built from its own source. The measured sections
exclude imports and separately declared supporting lemmas. Local lemmas within a
timed theorem are included. Run `lake test` to check supporting proofs and axiom
audits.

**Proof performance is more important than executable runtime performance.**
