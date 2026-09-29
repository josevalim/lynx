# Translation bug fixes

This file lists the bugs found in the Erlang/Elixir-to-Lean translation
pipeline, how each one was fixed, and where the fix is checked.

The pipeline has three stages:

1. `src/lynx_core_to_leanj.erl` turns Core Erlang (produced by the Erlang and
   Elixir compilers) into a JSON description of Lean syntax.
2. `lib/lynx/translation.ex` follows calls between modules, tracks purity and
   decides which calls go to the Lean runtime listed in `Lean/modules.json`.
3. `Lean/Lynx/Runner.lean` turns the JSON into Lean commands and elaborates or
   pretty-prints them. The generated code runs against the Lean runtime in
   `Lean/Erlang/` and `Lean/Lynx/`.

Behaviour of the Lean code is proved in
[`Lean/LynxTest/Regressions.lean`](Lean/LynxTest/Regressions.lean). That file
is written for readers who are new to Lean and explains every proof step. The
Erlang and Elixir stages are covered by ExUnit tests. Each new test fails on the
original code and passes after the fix.

## 1. `andalso/2` raised the wrong error (Lean runtime)

* **Where:** `Lean/Erlang/erlang/Guards.lean`, `Erlang.erlang.«andalso/2»`.
* **Bug:** a non-boolean left operand `V` raised `error(badarg)`. Erlang
  compiles `andalso` to a `case` whose fallback raises `error({badarg, V})`, so
  proofs about the exception disagreed with real programs.
* **Fix:** raise `.tuple #[.atom "badarg", V]`.
* **Proof:** `andalso_non_boolean_reports_value` proves the new behaviour for
  every non-boolean `V`. `andalso_true` and `andalso_false` show that the boolean
  cases did not change. The existing test `andalso_non_boolean` in
  `LynxTest/Tactic/Contracts.lean` was updated to the Erlang error term.

## 2. Negative integer literals made the runner fail (runner)

* **Where:** `Lean/Lynx/Runner.lean`, the `"integer"` node.
* **Bug:** the runner read integer nodes as natural numbers, so any negative
  literal, such as the pattern in `f(-1) -> ...` or the `-5` in `X + -5`, made
  the whole request fail with `Natural number expected`.
* **Fix:** read an `Int` and emit `(-n)` for negative values. This works both as
  a term and as a `match` pattern.
* **Proof:** the new fixture `test/fixtures/translations/literals.erl` is
  translated, rendered and verified by the existing integration and runner
  tests. Its Lean output is repeated in `Regressions.lean`, where
  `sign_minus_one`, `sign_one`, `sign_other` and `sign_float_is_not_minus_one`
  prove that the negative pattern and the negative constant behave as in Erlang.
  A build check fails if the copy stops matching the fixture.

## 3. Calls without arguments made the runner fail (translator)

* **Where:** `src/lynx_core_to_leanj.erl`, `apply_node/3`.
* **Bug:** `zero()` or `self()` was emitted as an application with no
  arguments, which the runner rejects (`application requires at least one
  argument`).
* **Fix:** a call without arguments is emitted as a plain reference to the
  zero-parameter Lean definition.
* **Proof:** `call_zero_returns_zero` and `call_zero_runs` in `Regressions.lean`,
  and the ExUnit test "translates zero-argument calls to plain references".

## 4. Calling a fun held in a variable crashed the translator (translator)

* **Where:** `src/lynx_core_to_leanj.erl`, the `c_apply` clause.
* **Bug:** `F(X)` has the Core form `apply F(X)` with a variable operator. The
  translator treated every variable operator as a module function name and
  crashed with an internal `badkey` error.
* **Fix:** only `{Name, Arity}` function names with matching argument counts
  are translated. Other applications are reported as unsupported Core with
  their source line. Looking up a missing function definition also reports
  unsupported Core instead of crashing.
* **Test:** "reports applications of fun variables as unsupported Core".

## 5. Qualified calls to undefined functions of the same module crashed (Elixir side)

* **Where:** `lib/lynx/translation.ex`, `remote_call/5`.
* **Bug:** `?MODULE:missing(X)` compiles in Erlang (it fails with `undef` when
  run). The translator treated it as a local call without checking that
  `missing/1` exists, and crashed with an internal `badkey` error.
* **Fix:** validate the function and raise the usual
  `undefined function :example.missing/1` compile error at the call site.
* **Test:** "validates qualified calls to the current module".

## 6. Unsupported clauses crashed while building the error message (translator)

* **Where:** `src/lynx_core_to_leanj.erl`, `clause/2`.
* **Bug:** a clause with a guard, such as `f(X) when X > 0 -> X`, was reported
  by pretty-printing the whole clause. The Core pretty printer cannot print a
  bare clause, so the translator crashed with a `FunctionClauseError` instead
  of reporting unsupported Core.
* **Fix:** report the guard, or the list of patterns when a clause has several.
* **Test:** "reports unsupported guards without crashing".

## 7. The runtime manifest listed functions the translator cannot call (manifest)

* **Where:** `Lean/ExportModules.lean` and the generated `Lean/modules.json`.
* **Bug:** every public `Erlang.*` definition whose name ends in an arity was
  exported. The translator calls exported functions with Erlang terms only, but
  `spawn/1` and `apply/2` also take the program's function table, and
  `andalso/2` takes unevaluated operands. Calls to them produced ill-typed Lean.
  `andalso/2` was also marked pure only because a theorem named
  `«andalso/2_pure»` exists, although that theorem has extra conditions.
* **Fix:** only functions of type `Lynx.Term → … → Lynx.Result`, with one term
  argument per arity, are exported. `modules.json` was regenerated with
  `lake env lean --run ExportModules.lean > modules.json`, which removed exactly
  these three entries.
* **Proof:** a check in `Regressions.lean` runs during the build. It reads
  `modules.json` and fails unless every listed function has the term signature
  and every function marked pure has an unconditional purity theorem. It also
  checks that the three functions are no longer listed. ExUnit test: "does not
  call runtime functions that need more than terms". Lake does not track
  `modules.json` as an input, so after editing it by hand, re-check with
  `lake env lean LynxTest/Regressions.lean` from `Lean/`.

## 8. Module names that are not Lean identifiers were emitted unquoted (translator)

* **Where:** `src/lynx_core_to_leanj.erl`, `module_name/1`.
* **Bug:** a module such as `'my-mod'` became the invalid Lean name
  `Erlang.my-mod`, and the runner rejected the request.
* **Fix:** components that are not plain identifiers are quoted, for example
  `Erlang.«my-mod»`. An Erlang module name containing dots is kept as a single
  component (`Erlang.«a.b»`). Plain names such as `Erlang.sum` and
  `Elixir.Foo.Bar` are unchanged.
* **Test:** "quotes module name components that are not identifiers".

## Related improvement: constant lists

The Erlang and Elixir compilers fold constant lists such as `[1, -2]` or
`[no, -1]` into one Core literal, which the translator reported as unsupported.
Such literals are now translated element by element into `Lynx.Term.cons`
cells, both as values and as patterns. `one_two_matches`,
`one_two_other_order` and `one_two_longer` in `Regressions.lean` prove that the
translated patterns and values behave as in Erlang.

## Checking everything

```console
mix test                 # Elixir tests, including the translation fixtures
cd Lean && lake test     # Lean tests, including LynxTest/Regressions.lean
```

The Lean proofs are checked by Lean's kernel. The proof audit at the end of
`Regressions.lean` rejects `sorry` and any axiom other than `propext`,
`Classical.choice` and `Quot.sound`.
