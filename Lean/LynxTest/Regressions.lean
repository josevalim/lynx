module

meta import Lean
meta import LynxTest.ProofAudit
public import Lynx
public import Erlang.erlang
import Erlang.lists
import Erlang.maps
import all Lynx.Term
import all Erlang.erlang.Guards

/-!
# Regression theorems for translation bugs

This file records bugs that were found in the Erlang/Elixir-to-Lean translation
pipeline and proves, with theorems that Lean's kernel checks, that the fixed
versions behave like Erlang. `BUGFIXES.md` at the repository root lists every
bug, including the ones in the Erlang and Elixir parts of the translator, which
are covered by ExUnit tests instead of Lean theorems.

## Reading this file if you are new to Lean

* A `theorem name : statement := proof` is a claim together with its proof.
  If this file compiles, every statement below is true; nothing is merely
  tested on a few examples.
* `Lynx.Term` is the Lean model of an Erlang term, for example
  `.integer (-1)` is the Erlang integer `-1` and `.atom "ok"` is the atom `ok`.
* A translated Erlang function returns a `Lynx.Result`. `.ok value` is a normal
  return and `.error (.error reason)` is `erlang:error(Reason)`.
* `rfl` ("reflexivity") proves an equation whose two sides compute to the same
  value, so `f x = .ok y := by rfl` literally runs `f x`.
* `simp` rewrites the goal with known equations (and the listed facts) until
  it is closed.
* `unfold f` replaces `f` by its definition; `split` then creates one goal per
  clause of a `match`.
* `omega` proves goals of linear integer arithmetic, such as `n + -5 = n - 5`.
* `example` is a theorem without a name, handy for concrete checks.
* `run_cmd` / `run_meta` blocks run Lean code while the file is compiled; a
  failure there stops the build, just like a failed proof.
-/

namespace LynxTest.Regressions
open Lynx

/-! ## Bug 1: `andalso/2` dropped the offending value

Erlang compiles `Left andalso Right` into a `case` on `Left` whose fallback
clause calls `erlang:error({badarg, Left})`. The Lean model used to raise the
bare atom `badarg`, so a proof about the error reason could disagree with the
real program. -/

/-- For every left operand `value` that is neither `true` nor `false`,
`value andalso Right` raises `error({badarg, value})` and never runs `Right`.

The two hypotheses `notTrue` and `notFalse` say that `value` is not a boolean.
Without them the statement would be false, since `true andalso Right` runs
`Right` (see `andalso_true` below). -/
theorem andalso_non_boolean_reports_value (value : Term) (right : Unit → Result)
    (notTrue : value ≠ .atom "true") (notFalse : value ≠ .atom "false") :
    Erlang.erlang.«andalso/2» (.ok value) right =
      .error (.error (.tuple #[.atom "badarg", value])) := by
  -- After unfolding, `simp` rules out the `true` and `false` clauses of the
  -- `match` using `notTrue` and `notFalse`, leaving the error clause.
  simp only [Erlang.erlang.«andalso/2», Result.ok_bind]

/-- A concrete instance: `1 andalso true` raises `error({badarg, 1})`. -/
example : Erlang.erlang.«andalso/2» (.ok (.integer 1)) (fun _ => .ok Term.true) =
    .error (.error (.tuple #[.atom "badarg", .integer 1])) := by
  rfl

/-- The fix did not change the boolean cases: `true andalso Right` is `Right`. -/
theorem andalso_true (right : Unit → Result) :
    Erlang.erlang.«andalso/2» (.ok (.atom "true")) right = right () := by
  rfl

/-- ... and `false andalso Right` is `false` without running `Right`. -/
theorem andalso_false (right : Unit → Result) :
    Erlang.erlang.«andalso/2» (.ok (.atom "false")) right = .ok Term.false := by
  rfl

/-! ## Bugs 2 and 3: negative literals and zero-argument calls
(and the new support for constant lists)

The Erlang module `test/fixtures/translations/literals.erl` is

```erlang
sign(-1) -> minus_one;
sign(X) -> X + -5.

zero() -> 0.

call_zero(_) -> zero().

one_two([1, -2]) -> yes;
one_two(_) -> [no, -1].
```

Before the fixes the translation pipeline could not produce Lean for it at all:

* the JSON-to-Lean runner only accepted natural numbers, so `-1` and `-5` made
  the whole request fail with "Natural number expected";
* a call without arguments such as `zero()` (or `self()`) was emitted as an
  application with no arguments, which the runner rejects;
* the Erlang compiler folds constant lists such as `[1, -2]` into one literal,
  which the translator reported as unsupported.

The definitions below are the translator's output for that module, copied from
`test/fixtures/translations/literals.lean` (only the namespace differs). The
ExUnit integration test checks that the translator still produces exactly that
file. The theorems then show that this Lean code computes what Erlang computes. -/

namespace Literals

#lynx_pure
  public def «one_two/1» (_0 : Lynx.Term) : Lynx.Result :=
    match _0 with
    |
    Lynx.Term.cons (Lynx.Term.integer 1) (Lynx.Term.cons (Lynx.Term.integer (-2)) Lynx.Term.nil) =>
      Lynx.Result.ok (Lynx.Term.atom "yes")
    | _3 =>
      Lynx.Result.ok
        (Lynx.Term.cons (Lynx.Term.atom "no")
          (Lynx.Term.cons (Lynx.Term.integer (-1)) Lynx.Term.nil))

#lynx_pure
  public def «sign/1» (_0 : Lynx.Term) : Lynx.Result :=
    match _0 with
    | Lynx.Term.integer (-1) => Lynx.Result.ok (Lynx.Term.atom "minus_one")
    | vX => Erlang.erlang.«+/2» vX (Lynx.Term.integer (-5))

#lynx_pure
  public def «zero/0» : Lynx.Result :=
    Lynx.Result.ok (Lynx.Term.integer 0)

#lynx_pure
  public def «call_zero/1» (_0 : Lynx.Term) : Lynx.Result :=
    «zero/0»

/- Guard against the copy above drifting from the fixture: the build fails
unless the definitions in the fixture appear verbatim in this file. -/
run_cmd do
  let root ← if ← System.FilePath.pathExists "LynxTest" then pure "" else pure "Lean/"
  let fixture ← IO.FS.readFile (root ++ "../test/fixtures/translations/literals.lean")
  let this ← IO.FS.readFile (root ++ "LynxTest/Regressions.lean")
  let body := ((fixture.splitOn "namespace Erlang.literals\n")[1]!.splitOn
    "end Erlang.literals")[0]!
  unless (this.splitOn body).length > 1 do
    throwError "LynxTest/Regressions.lean no longer matches literals.lean"

/-- `sign(-1)` selects the first clause: the pattern `(-1)` matches the
negative integer `-1`. -/
theorem sign_minus_one : «sign/1» (.integer (-1)) = .ok (.atom "minus_one") := by
  rfl

/-- The pattern matches only `-1`: the positive integer `1` takes the second
clause, and the literal `-5` really is negative, so `sign(1)` is `1 + -5 = -4`. -/
theorem sign_one : «sign/1» (.integer 1) = .ok (.integer (-4)) := by
  rfl

/-- For every integer `n` other than `-1`, `sign(n)` returns `n - 5`, exactly as
the second Erlang clause `sign(X) -> X + -5` does.

`unfold` replaces `sign/1` by its body and `split` produces one goal per
`match` clause. The first clause would need `n = -1`, which contradicts `hn`.
In the second clause the library rule `«+/2_integers»` computes the integer
addition, and `omega` proves the remaining arithmetic `n + -5 = n - 5`. -/
theorem sign_other (n : Int) (hn : n ≠ -1) :
    «sign/1» (.integer n) = .ok (.integer (n - 5)) := by
  unfold «sign/1»
  split
  · rename_i matched
    exact absurd (Term.integer.inj matched) hn
  · simp only [Erlang.erlang.«+/2_integers», Result.ok_inj, Term.integer.injEq]
    omega

/-- Erlang pattern matching is exact: the float `-1.0` does not match the integer
pattern `-1`, so it reaches `X + -5` instead of returning `minus_one`. -/
theorem sign_float_is_not_minus_one (value : Term.FiniteFloat) :
    «sign/1» (.float value) = Erlang.erlang.«+/2» (.float value) (.integer (-5)) := by
  rfl

/-- `call_zero(X)` returns `0` for every argument: the zero-argument call
`zero()` became the plain reference `«zero/0»`. -/
theorem call_zero_returns_zero (input : Term) :
    «call_zero/1» input = .ok (.integer 0) := by
  rfl

/-- The same holds when the call is executed by the process runtime from a
fresh environment: it returns `0` and leaves the environment unchanged. -/
theorem call_zero_runs (input : Term) :
    Lynx.run («call_zero/1» input) = .ok (.integer 0) {} := by
  simp [Lynx.run, call_zero_returns_zero]

/-- The Erlang list `[1, -2]` is the Lean term
`.cons (.integer 1) (.cons (.integer (-2)) .nil)`; it matches the first clause. -/
theorem one_two_matches :
    «one_two/1» (.cons (.integer 1) (.cons (.integer (-2)) .nil)) = .ok (.atom "yes") := by
  rfl

/-- Order matters: `[-2, 1]` is a different list, so `one_two([-2, 1])` returns
the constant list `[no, -1]` from the second clause. -/
theorem one_two_other_order :
    «one_two/1» (.cons (.integer (-2)) (.cons (.integer 1) .nil)) =
      .ok (.cons (.atom "no") (.cons (.integer (-1)) .nil)) := by
  rfl

/-- A longer list that merely starts with `1, -2` does not match either,
because the pattern requires the tail to be the empty list `[]`. -/
theorem one_two_longer :
    «one_two/1» (.cons (.integer 1) (.cons (.integer (-2)) (.cons (.integer 3) .nil))) =
      .ok (.cons (.atom "no") (.cons (.integer (-1)) .nil)) := by
  rfl

end Literals

/-! ## Bug 4: the runtime manifest exported functions the translator cannot call

`Lean/modules.json` tells the translator which Erlang functions are implemented
in Lean. The translator calls each of them as `Module.«name/arity» arg₁ … argₙ`
with Erlang terms. `spawn/1` and `apply/2` also need the program's function
table and `andalso/2` takes unevaluated operands, so calling them that way
produced ill-typed Lean. The manifest also claimed that `andalso/2` is pure only
because a theorem named `«andalso/2_pure»` exists, although that theorem is
conditional.

The check below runs while this file is compiled. It reads `modules.json` and
fails the build unless every listed function

* exists in Lean,
* has exactly the type `Lynx.Term → … → Lynx.Result` with one argument per arity,
* and, when marked pure, has a `_pure` theorem stating unconditionally that
  every call is pure (`Lynx.Result.IsPure`).

It also checks that the three functions above are no longer listed. -/

open Lean Meta in
run_meta do
  let path ← if ← System.FilePath.pathExists "modules.json" then pure "modules.json"
    else pure "Lean/modules.json"
  let manifest ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let modules ← IO.ofExcept manifest.getObj?
  let termType := mkConst ``Lynx.Term
  let resultType := mkApp (mkConst ``Lynx.Result) termType
  let mut listed : Array Name := #[]
  for (moduleName, functions) in modules.toArray do
    for (functionName, entry) in (← IO.ofExcept functions.getObj?).toArray do
      let name := Name.str (Name.str `Erlang moduleName) functionName
      listed := listed.push name
      let some info := (← getEnv).find? name
        | throwError "manifest lists unknown function {name}"
      let some arity := (functionName.splitOn "/").getLast!.toNat?
        | throwError "manifest entry without arity: {name}"
      forallTelescope info.type fun arguments body => do
        unless arguments.size == arity do
          throwError "{name} takes {arguments.size} arguments, expected {arity}"
        for argument in arguments do
          unless ← isDefEq (← inferType argument) termType do
            throwError "{name} has a non-term parameter"
        unless ← isDefEq body resultType do
          throwError "{name} does not return Lynx.Result"
        if (← IO.ofExcept (entry.getObjValAs? Bool "pure")) then
          let proofName := Name.str (Name.str `Erlang moduleName) (functionName ++ "_pure")
          let some proof := (← getEnv).find? proofName
            | throwError "{name} is marked pure without {proofName}"
          let expected ← mkForallFVars arguments
            (← mkAppM ``Lynx.Result.IsPure #[mkAppN (mkConst name) arguments])
          unless ← isDefEq proof.type expected do
            throwError "{proofName} does not state unconditional purity"
  for excluded in [``Erlang.erlang.«spawn/1», ``Erlang.erlang.«apply/2»,
      ``Erlang.erlang.«andalso/2»] do
    if listed.contains excluded then
      throwError "{excluded} must not be listed in modules.json"

end LynxTest.Regressions

run_cmd do
  LynxTest.ProofAudit.checkModule `LynxTest.Regressions
