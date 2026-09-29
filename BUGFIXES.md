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
Erlang and Elixir stages are covered by ExUnit tests. Regression checks cover the
previous failures; positive checks also protect behavior that already worked.

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
* **Fix:** distinguish named module calls from calls through function values.
  Named calls require a `{Name, Arity}` operator with a matching argument count;
  a missing definition or malformed named call reports unsupported Core.
  Upstream now translates `F(X)` through `Lynx.Term.apply` and a generated
  function table, replacing this PR's original unsupported-call diagnostic.
* **Tests:** "dynamic application makes local, remote, and recursive callers
  impure", "reports missing named definitions and mismatched arities as
  unsupported Core", and the `functions` translation fixture.

## 5. Qualified calls to undefined functions of the same module crashed (Elixir side)

* **Where:** `lib/lynx/translation.ex`, `remote_call/6`.
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
* **Fix:** report the unsupported guard itself. Upstream now supports clauses
  with several patterns, so those use the normal translation path.
* **Test:** "reports unsupported guards without crashing".

## 7. The runtime manifest listed functions the translator cannot call (manifest)

* **Where:** `Lean/ExportModules.lean` and the generated `Lean/modules.json`.
* **Bug:** every public `Erlang.*` definition whose name ends in an arity was
  exported. The translator calls exported functions with Erlang terms only, but
  the old `spawn/1` and `apply/2` took an extra function-table argument, while
  `andalso/2` takes unevaluated operands. Calls to them produced ill-typed Lean.
  `andalso/2` was also marked pure only because a theorem named
  `«andalso/2_pure»` exists, although that theorem has extra conditions.
* **Fix:** only functions of type `Lynx.Term → … → Lynx.Result`, with one term
  argument per arity, are exported. After the upstream sync, `spawn/1` and
  `apply/2` have compatible signatures: the runtime resolves the table separately.
  Regenerating `modules.json` restores both as impure builtins. `andalso/2`
  remains excluded because its signature still does not fit.
* **Proof:** a check in `Regressions.lean` runs during the build. It reads
  `modules.json` and fails unless every listed function has the term signature
  and every function marked pure has an unconditional purity theorem. It also
  checks that `andalso/2` is absent and `spawn/1` and `apply/2` are present and
  impure. ExUnit test: "does not call runtime functions that need more than terms".
  Lake does not track
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
* **Tests:** "quotes module name components that are not identifiers", "quotes
  trailing newlines instead of aliasing module names", and "rejects module names
  that can escape Lean identifier quotes". Review added the last two checks:
  the regular expression must match the entire component, and an embedded `»`
  must be rejected instead of closing the generated quote early.

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

## A Lean 4 beginner's walkthrough

This section explains how to read the fixes and their proofs. You do not need to
know Lean tactics in advance. Start with the translation pipeline, then read the
small proof below before opening the larger regression file.

### 1. Follow one function through the pipeline

Consider this Erlang code from the `literals` fixture:

```erlang
sign(-1) -> minus_one;
sign(X) -> X + -5.
```

The Erlang compiler first converts source code into **Core Erlang**, a smaller
language with explicit operations such as cases, calls, variables, and literals.
`src/lynx_core_to_leanj.erl` reads that structure and produces JSON describing
Lean syntax. The JSON is an intermediate representation, not the result of
running `sign`.

`lib/lynx/translation.ex` discovers the functions and modules that must be
translated. It also decides which calls can use the existing Lean runtime.
`Lean/modules.json` is the list of available runtime calls and their purity flags.

`Lean/Lynx/Runner.lean` reads the JSON and builds Lean syntax. Its two commands
answer different questions:

- `render` pretty-prints the syntax into a Lean source file. Success means that
  rendering succeeded; it does not mean the generated program has been proved.
- `verify` elaborates the syntax: Lean resolves names, checks types, and checks
  any proof declarations generated with it. It does not invent a correctness
  theorem for every translated function.

The fixture tests check translation, rendering, and verification. Separately,
[`Regressions.lean`](Lean/LynxTest/Regressions.lean) states properties of the
translated functions and supplies proofs. These layers are complementary: a
proof about a hand-written Lean function alone would not test the translator.

### 2. Read the types before reading the tactics

Erlang values can have different kinds at runtime. Lean represents those kinds
with the constructors of `Lynx.Term`, defined in
[`DataTypes.lean`](Lean/Lynx/Term/DataTypes.lean).

| Erlang value | Lean representation | What to notice |
| --- | --- | --- |
| `-1` | `Term.integer (-1)` | The payload is an `Int`, which supports negative numbers. |
| `ok` | `Term.atom "ok"` | The string stores the atom's name. |
| `true` | `Term.atom "true"` | An Erlang boolean is modeled as an atom, not Lean's `Bool`. |
| `[]` | `Term.nil` | This is an Erlang term, not Lean's native empty `List`. |
| `[1, -2]` | `Term.cons (.integer 1) (.cons (.integer (-2)) .nil)` | Each cell contains a head and a tail. |
| `{badarg, 1}` | `Term.tuple #[.atom "badarg", .integer 1]` | `#[...]` is Lean's array notation, used for tuple elements. |

A leading dot, as in `.integer 1`, lets Lean infer the constructor's type from
context. It abbreviates `Term.integer 1`; it does not introduce a different value.

A translated function normally returns `Result`, which defaults to
`Result Term`. A **term** is a value; a **result** describes a computation that
may return a value, raise an exception, or request an effect. For example:

- `.ok (.integer 0)` is a computation that returns the integer zero.
- `.error (.error (.atom "badarg"))` is a computation that raises an Erlang
  `error` exception. The outer constructor belongs to `Result`; the inner one
  belongs to `Exception`. The nested spelling is intentional.
- Operations such as sending a message have other `Result` constructors.
  `Lynx.run` interprets a computation in a process environment and returns an
  `Outcome`, which also records the resulting environment.

This distinction explains why a theorem about `Result.ok` does not necessarily
mention process state, whereas `call_zero_runs` checks an `Outcome` from a fresh
environment as well.

### 3. A complete first proof

After `mix setup` has built the project, save the following as
`/tmp/FirstProof.lean`. From the project's `Lean/` directory, run
`lake env lean /tmp/FirstProof.lean`.

```lean
module

public import Lynx

namespace FirstProof
open Lynx

#lynx_pure
public def zero (_input : Term) : Result :=
  .ok (.integer 0)

theorem zero_returns_zero (input : Term) :
    zero input = .ok (.integer 0) := by
  rfl

end FirstProof
```

Read the declaration from left to right:

- `def zero` introduces an implementation. Its argument has type `Term`, and
  its result has type `Result`.
- `:=` starts the implementation or proof body.
- `theorem zero_returns_zero` names a proposition together with its proof.
- `(input : Term)` introduces an arbitrary input. The theorem therefore covers
  every `Term`, not only integer zero or a selected test input.
- After `:`, the equality is the claim to prove. After `by`, the tactics construct
  the proof.
- `rfl` asks Lean to check that both sides are equal by definition. Expanding
  `zero input` gives exactly the right-hand side. It does not execute the Erlang
  VM or compare a sample of inputs.

`#lynx_pure` generates a proof that this function has no modeled process effects.
Purity does **not** mean “cannot raise”: an error result is also pure. Nor does
this annotation prove the particular return value; that is the job of
`zero_returns_zero`.

`module` enables Lean's explicit module visibility rules. `public def` exports
this example function, and `public import` deliberately re-exports an imported
API. The theorem is private to this module by default. In the real tests,
`import all` makes implementation details available when a proof needs them;
it does not mean those details should become part of the public library API.

### 4. Understand the arithmetic proof in the regression file

The important general statement is `sign_other`, inside the `Literals`
namespace. Its declaration begins:

```lean
theorem sign_other (n : Int) (hn : n ≠ -1) :
    «sign/1» (.integer n) = .ok (.integer (n - 5)) := by
```

`n : Int` means any integer. `hn : n ≠ -1` is a named hypothesis excluding the
special first clause. The guillemets in `«sign/1»` quote a Lean identifier that
contains a slash; `/1` is part of the name and records the Erlang arity.

Here is the proof from that file:

```lean
  unfold «sign/1»
  split
  · rename_i matched
    exact absurd (Term.integer.inj matched) hn
  · simp only [Erlang.erlang.«+/2_integers», Result.ok_inj, Term.integer.injEq]
    omega
```

These are excerpts in the regression file's context, not a second standalone
program. Follow how each line changes the problem:

1. `unfold` replaces the function call with its definition, exposing the match
   on the input term.
2. `split` considers the match's possible branches. Each `·` introduces the
   proof for one branch.
3. The first branch says the integer input matched `-1`. `rename_i matched`
   gives its generated equality a readable name. `Term.integer.inj` extracts
   equality of the integer payloads from equality of two integer terms.
   That equality contradicts `hn`, so `absurd` closes this impossible branch.
4. In the other branch, `simp only` uses the listed equations to simplify the
   runtime addition and constructor equalities. Restricting the rule list makes
   the proof's dependencies explicit.
5. `omega` finishes the integer arithmetic. Like the other tactics, it produces
   proof evidence for Lean's kernel to check.

The other theorems fill different roles. `sign_minus_one` proves the special
case; `sign_one` is a concrete positive-input check. The float theorem says that
an integer pattern does not match a float constructor. It does not claim a
complete numeric theorem about floating-point addition.

### 5. Connect each fix to the behavior being checked

**Short-circuit conjunction.** The right operand of `andalso/2` has type
`Unit → Result`. This is a delayed computation, often called a *thunk*. `Unit`
has the single value `()`, so `right ()` runs the delayed computation. The left
operand is already a `Result`. The implementation inspects its returned term:
`true` runs the right side, `false` returns false, and any other term becomes
part of `error({badarg, value})`. The right side may return any Erlang term;
`true andalso 99` returns `99`. A bad left operand must not evaluate the right.
The regression statements quantify over an arbitrary `right`, so they protect
this short-circuit behavior rather than checking only one chosen right operand.

**Negative integers.** `Nat` represents nonnegative integers; `Int` represents
signed integers. The old JSON reader used `getNat?`, so it failed before Lean
could check a negative value. `getInt?` reads the signed value, and `natAbs`
provides the nonnegative digits for the numeric token. For a negative value the
runner constructs syntax for `(-n)`. Parentheses keep that expression together
as an argument and allow it to appear in an integer pattern. This change does
not mean the translator now supports every numeric literal kind; float literals
are a separate translation feature.

**Calls without arguments.** In Lean, a definition such as `«zero/0» : Result`
is already a value describing a computation. Referring to it needs no argument
list. The translator must emit an identifier rather than an application node
with zero arguments. This differs from the `Unit → Result` thunk above, which
really does require the argument `()`. The rule also applies to a zero-arity
runtime call such as `self/0`; its lack of arguments does not make it pure.

**Calls through function variables.** Core distinguishes a named module
function, represented by `{Name, Arity}`, from a variable containing a function.
The direct-call path can translate only the former. Checking the operator shape
and argument count avoids trying to look up an ordinary variable as a module
function. Upstream now provides a second path: `F(X)` becomes `Term.apply`,
which requests a dynamic call. A function term carries an ID, its arity, and
captured values. The generated `Erlang.program.fun_table` maps IDs to Lean
implementations. Pass that table to `Lynx.run` to execute the call. The runtime
checks the function and arity and uses `callDepth` to bound nested dynamic
calls; exhausting that bound produces `Outcome.exhausted`, not an Erlang
exception. Dynamic calls remain conservatively impure even when a particular
function body has no effects.

**Qualified calls to the current module.** `?MODULE:missing(X)` enters the
remote-call path even though the named module is the current one. Before handing
it back to local translation, the Elixir layer now checks that the definition
exists. The error uses the call site's file and line. This is a translator
`CompileError`, not a Lean `Result.error` and not a proof of Erlang's runtime
`undef` behavior. Keeping these kinds of failure separate makes the diagnostic
and the scope of the fix easier to understand.

**Unsupported guards.** A Core clause contains patterns, a guard, and a body.
The Core pretty-printer cannot print a bare clause as an expression. Passing it
the guard gives it an expression it can print. Multiple patterns now translate
normally; guarded clauses still report the offending guard, whether they have
one pattern or several. This repairs error reporting; it does not add guard
translation.
The ExUnit tests check the diagnostic text and source line because these are
properties of the translator running on the BEAM VM.

**Runtime manifest.** Lean function arrows describe the arguments one by one:
`Term → Term → Result` takes two term arguments and returns a computation. The
exporter now checks both this shape and the arity in the function's name.

| Runtime function | Why it can or cannot be exported |
| --- | --- |
| `+/2` | Two `Term` arguments and a `Result`; it fits the calling convention. |
| `self/0` | No arguments and a `Result`; it fits, although it is impure. |
| `spawn/1`, `apply/2` | Now take only terms and return a `Result`; exported as impure. The runtime resolves the table later. |
| `andalso/2` | Takes a computation and a thunk, rather than two term arguments. |

A function's Erlang-looking name is therefore not enough to make it callable by
the translator. Excluding a function from this manifest does not delete its
Lean implementation. The regression module also checks each listed declaration
and, for entries marked pure, checks that the `_pure` theorem asserts purity
without extra hypotheses. A conditional theorem such as “if both operands are
pure, then this conjunction is pure” does not justify an unconditional flag.

**Module names.** Lean uses dots between namespace components. The Erlang atom
`'a.b'` is one module name, so it must become `Erlang.«a.b»`, not two nested
components. Hyphens and spaces likewise need quoting. Elixir module names have
an existing dot-separated naming convention, so their components are handled
separately.

Review found an additional boundary case: in the regular expression engine,
`$` normally matches either the end of the input or the position before a final
newline. The atom written `:"demo\n"` in Elixir could therefore be emitted as
`Erlang.demo` followed by whitespace. Lean reads that as the same identifier as
`Erlang.demo`, losing part of the original name. The `dollar_endonly` option
requires the check to consume the full component, so this name is quoted and
remains distinct. The added regression covers both Erlang and Elixir names.
The Erlang compiler used for this review rejects control characters in source
module names. This additional check protects the name-conversion API when it is
called directly or receives constructed Core; it is not a claim that such a
module can be compiled from ordinary Erlang source.

A second review case explains why wrapping text in quotes is not enough. The
module atom written `:"erlang» -- "` would become `Erlang.«erlang» -- »`.
The embedded `»` closes the name early, and `--` starts a Lean comment. Lean
then reads the identifier as `Erlang.erlang`, which is a different module name.
Lean's identifier syntax has no escape for a closing `»` inside a quoted
component. The converter now rejects such a component with
`{unsupported_lean_module_name, Name}` before emitting Lean syntax. This is a
name-conversion error, not an Erlang exception modeled by `Result`.

**Constant lists.** The compiler may fold a whole literal list into one Core
node. The translator recursively expands that node into `Term.cons` cells.
The tail of a `Term.cons` is itself a `Term`, which also permits Erlang improper
lists such as `[1 | no]`. Exact list patterns still require the specified tail:
`[1, -2, 3]` does not match `[1, -2]`. This is separate from Lean's native
`List Int`, whose tail is always another list.

### 6. Know exactly what a passing check guarantees

| Check | What it establishes | What it does not establish |
| --- | --- | --- |
| ExUnit translator tests | Expected JSON and diagnostics for the tested Core inputs. | Correctness of the translator for every possible Erlang program. |
| Fixture rendering tests | Expected Lean text for the checked fixtures. | A semantic theorem merely from rendering text. |
| Runner verification tests | The fixture syntax and generated declarations elaborate successfully. | An unstated return-value or equivalence property. |
| Regression theorems | The exact propositions written in those theorems, including any hypotheses. | Properties of inputs or language features outside those statements. |
| Manifest/fixture build checks | The current manifest has the required signatures and purity claims, and the copied fixture body matches. | Automatic rechecking after every external file edit. |
| Proof audit | Proof dependencies use only the project's allowed axioms. | An axiom-free proof or a verified implementation of the Erlang compiler. |

The allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`, which are
standard foundations used by this Lean project. `sorryAx` is not allowed.
A tactic is a way of constructing a proof; the kernel checks the result. The
`run_cmd` and `run_meta` blocks perform additional build-time checks, including
file reads and inspection of declarations. Those checks are useful, but should
not be described as formal proofs that the entire translation pipeline is
correct.

Some boundaries remain deliberate: guarded clauses are unsupported, and module
components containing Lean's closing quote delimiter `»` are explicitly rejected.
Function-variable calls are now supported through the generated table, with a
bound on nested dispatch. These fixes do not remove the project's broader
semantic limitations.

### 7. Reproduce the checks and extend them safely

From the repository root:

```console
mix setup
mix format --check-formatted
mix test
```

Then, from the `Lean/` directory:

```console
lake test
lake env lean LynxTest/Regressions.lean
lake env lean --run ExportModules.lean > /tmp/lynx-modules-review.json
diff -u modules.json /tmp/lynx-modules-review.json
```

Compare JSON contents if the final command reports only whitespace differences.
The temporary export lets you check the manifest without overwriting the tracked
file before the comparison. A successful export command alone is not evidence
that the tracked manifest is up to date.

Run `Regressions.lean` directly after changing `modules.json` or the literal
fixture. Lake does not track those `IO.FS.readFile` inputs as ordinary Lean
module dependencies, so a cached test build may not rerun the checks. Changing
only a file that a build-time command reads is different from changing a Lean
module that another module imports.

If many Lean runner processes strain your machine, the same ExUnit suite can
run with `ERL_FLAGS="+S 2:2" mix test --max-cases 2`. This limits concurrency;
it does not remove tests.

For a new regression, write down the failing input, decide which pipeline stage
owns the behavior, and make the smallest check that observes it. Use an ExUnit
test for translation or diagnostics, and a Lean theorem for a property of the
Lean model. State the input domain and any hypotheses explicitly. Where a
fixture connects the two, verify that the generated code is the code being
proved. First observe the regression fail, then repair the implementation and
run the relevant checks again.

The existing verification benchmarks are run from `Lean/` with
`sh Benchmarks/run.sh 5`. They measure proof elaboration after imports, not
Erlang execution speed. A passing benchmark proof is still a proof check; its
elapsed time is a separate measurement and needs repeated runs and a comparable
baseline before drawing a performance conclusion.

### 8. Review and validation record before the upstream sync — 2026-09-29

This record describes commit `d3098aa`, before the upstream sync described below.

The review followed the changed paths from Core translation through JSON,
Lean syntax construction, manifest exports, and regression statements. It found
and repaired two additional cases in the module-name fix: trailing newlines
could lose their identity, and an embedded closing quote could expose suffix
text as Lean syntax. Both added ExUnit tests were observed failing before their
corresponding fixes and passing afterward. The documentation's earlier blanket
claim that every added test failed on the old code was also corrected: some
checks intentionally protect previously working behavior.

Validation used Lean 4.33.1, Elixir 1.20.4, and Erlang/OTP 29:

- A fresh `lake test` build passed, including the regression proofs, axiom
  audits, and public API snapshot.
- The final ExUnit suite passed all **42 tests** with two schedulers and at most
  two concurrent test cases. Compilation with `--warnings-as-errors`, formatting,
  and Git whitespace checks passed.
- The exporter reproduced the tracked manifest's JSON contents. Two temporary
  mutations were rejected by the direct regression check: adding `spawn/1`
  with its incompatible signature, and marking `self/0` pure without a purity
  theorem. The original manifest was restored and rechecked successfully.
- Additional translation/render/verification probes covered ordinary, hyphenated,
  dotted, spaced, Unicode, underscore, and Elixir namespace components. Separate
  Lean parser checks reproduced the two name-aliasing cases described above.
- Additional probes checked an integer beyond 128-bit magnitude, zero-arity
  local and runtime calls, and nested/improper list values and patterns. Four
  equations appended to the rendered Lean source compiled successfully.
- Erlang evaluation confirmed `{badarg, 1}` for `1 andalso true`, that a false
  left operand skips an error-raising right operand, and that
  `true andalso 99` returns `99`.
- The complete `FirstProof.lean` example in this guide compiled successfully.

The verification benchmark comparison used five alternating runs per revision,
with each revision's Lean libraries built from its own sources. The baseline's
Lean files from `a82ee2d` were checked to match `main` at `3c7fa13` byte for byte.
All **140 timed proof checks** passed. Translated proof medians ranged from
8.5% faster to 1.7% slower; `sum-append` changed from 1443.48 ms to 1453.75 ms
(+0.7%). Native control medians varied from 10.4% faster to 10.0% slower. These
measurements show no substantial slowdown in this suite, but do not establish a
general speedup or replace the correctness checks above.

### 9. Upstream compatibility update — 2026-09-29

PR #2 now includes upstream `main` through
[`eaa0fd3`](https://github.com/josevalim/lynx/commit/eaa0fd37121dc42179c6e6c2680b815000bc2973).
The preceding upstream commit, `9ca5a34`, adds anonymous functions, captured
values, dynamic dispatch, and a generated function table. This changes two of
the original fixes' expected outcomes: function-variable calls now translate
successfully, and `spawn/1` and `apply/2` are callable runtime exports.

For a Lean beginner, the key distinction is between **describing a call** and
**executing its implementation**. A translated `F(X)` creates a `Result.apply`
request. The `Term.function` value identifies the implementation and carries
captured values, such as `X` in `fun(Y) -> X + Y end`. The generated
`Erlang.program.fun_table` stores adapters that combine those captures with the
new arguments. `Lynx.run computation [] Erlang.program.fun_table` resolves these
requests and runs the computation; the empty list selects the default schedule.
Its default `callDepth` is 100. A nested dynamic call consumes depth, and reaching
zero produces `Outcome.exhausted`. This outcome is a modeling limit, separate
from an Erlang exception or a successful return.

The merge preserves upstream's implementation and adjusts these boundaries:

- Named local calls still validate their operator and argument count, and a
  missing definition reports unsupported Core. Function values follow the new
  dynamic path. The obsolete test expecting `F(X)` to fail was replaced by
  upstream's broader dynamic-call and purity tests; a new test protects missing
  named definitions and mismatched arities.
- Generated anonymous helpers use `translate_def/3` with their actual body.
  Ordinary named functions use the checked lookup in `translate_def/2`. Both
  paths retain the evolving function table, so discovering one function does
  not discard previously discovered functions.
- Multiple match inputs and patterns use JSON arrays named `expressions` and
  `patterns`. The `literals` JSON fixture was regenerated for that format. Its
  rendered Lean definitions are unchanged, so the existing proofs still apply
  to exactly the generated code.
- Guard diagnostics report the guard expression itself for both one-pattern
  and multiple-pattern clauses. A supported multiple-pattern clause is no longer
  mistaken for an unsupported construct.
- Upstream removes `Erlang/erlang/Fun.lean`, places `apply/2` in
  `Erlang/erlang.lean`, and places `spawn/1` in `Erlang/erlang/Process.lean`.
  Both functions now take only term arguments. The regenerated manifest includes both with
  `pure: false`, while `andalso/2` remains excluded. The build check now asserts
  these current expectations as well as checking all signatures and purity
  claims.

The earlier validation record above is historical: its 42-test count and its
exclusion of `spawn/1` describe the pre-sync revision, not this runtime.

Validation after resolving the merge, with the same Lean 4.33.1, Elixir 1.20.4,
and Erlang/OTP 29 toolchains:

- A clean `lake build` followed by `lake test` passed all 46 build jobs,
  including the existing and new upstream theorems, proof audits, runtime
  dispatch tests, regression proofs, and public API snapshot.
- All **45 ExUnit tests** passed. Compilation with `--warnings-as-errors`,
  formatting, and Git whitespace checks passed.
- The exporter reproduced the tracked manifest. Temporarily removing `spawn/1`
  made the new required-export check fail; adding `andalso/2` made the signature
  check fail. The original manifest was restored and the direct regression
  check passed afterward.
- Extra translation/render/verification probes passed for seven module-name
  shapes, a negative integer beyond 128-bit magnitude, zero-arity calls, and
  nested/improper lists. The four concrete equations appended to the generated
  literal code still compiled, as did the guide's `FirstProof.lean` example.
- A separate generated program combined a quoted module name, a captured
  variable, a dynamic call with `-5`, and a zero-arity anonymous function passed
  to `spawn/1`. Both generated files verified. Evaluation with the generated
  table returned `5` for a captured `10` plus `-5`, and returned the child PID
  for the spawn. These are concrete execution checks, separate from the
  project's general runtime theorems.

The runtime changes were also measured against the preceding PR commit,
`d3098aa`, using five alternating benchmark runs per revision on the same
machine. Each revision's libraries were built from its own source tree; only
final proof elaboration was timed. All **140 timed proof checks** passed.

| Translated proof | Before (median ms) | After (median ms) | Change |
| --- | ---: | ---: | ---: |
| Sum contract | 345.02 | 336.63 | -2.4% |
| Sum append | 1481.44 | 1558.01 | +5.2% |
| Reverse contract | 26.35 | 27.48 | +4.3% |
| Reverse involution | 21.27 | 21.31 | +0.2% |
| Reverse append | 178.22 | 181.20 | +1.7% |
| Sets union contract | 253.99 | 208.80 | -17.8% |
| Sets union commutativity | 160.08 | 138.06 | -13.8% |
| Sets union empty identity | 42.14 | 41.61 | -1.3% |

The largest measured translated-proof slowdown was `sum-append`, about 77 ms
(+5.2%). Native control medians ranged from 10.2% faster to 14.6% slower. These
runs found no proof failures and no large translated-proof slowdown; the timing
variation does not establish a general performance improvement.
