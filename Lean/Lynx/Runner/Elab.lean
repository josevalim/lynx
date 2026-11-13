module

public meta import Lean
public import Lynx.Term.Bitstring.Matching
public import Lynx.Term.Except
public import Lynx.Concurrent.Trace

/-! Elaborators and simplification procedures for translated programs and their proofs.

They depend on Lean's elaborator, so they live here rather than in `Lynx`.
The runner imports this module alongside `Lynx` for translated code and laws,
which keeps the library itself free of Lean's elaborator, for example in
`lake check` exports.

## Simplification

Simp simplifies the arguments of an application before rewriting it, so the
continuations of a bind, guard, or handler are simplified before the computation
selects one of them. Matches on their unknown values are stuck, and simp tries
each overlapping case by discharging its hypotheses, which fails. Instead, these
procedures simplify the computation first and, when it returns, continue with
the selected branch only.

## Termination

Recursion over the bits left by an extraction, such as bitstring generators,
decreases `sizeOf` by the consumed bits. Bitstring extractions continue through
`extract`, whose well-founded preprocessing passes the extraction's
equation to its continuation. Lean's default `decreasing_tactic` tries
`decreasing_trivial`, which this extends. -/

namespace Lynx.Except

public section Simplification
open Lean Meta Simp

/-- Simplify the computation at argument `index` of `e`. When it returns a value,
rewrite `e` with `lemma`, applied to the value and the arguments after it. -/
private meta def onReturn (e : Expr) (index : Nat) (lemma : Name) : SimpM Step := do
  let args := e.getAppArgs
  let some computation := args[index]? | return .continue
  let result ← simp computation
  let_expr Except.ok _ _ value := result.expr | return .continue
  -- Leave applications the lemma does not describe, such as other instances, to simp.
  try
    let step ← mkAppM lemma (#[value] ++ args[(index + 1):])
    let some (_, _, rhs) := (← inferType step).eq? | return .continue
    let proof ← match result.proof? with
      | none => pure step
      | some proof =>
        let motive ← withLocalDeclD `computation (← inferType computation) fun replaced =>
          mkLambdaFVars #[replaced] (mkAppN e.getAppFn (args.set! index replaced))
        mkEqTrans (← mkCongrArg motive proof) step
    return .visit { expr := rhs.headBeta, proof? := some proof }
  catch _ => return .continue

/-- A bind whose computation returns continues with the value. -/
simproc ↓ bindReturned (@Bind.bind (Except Exception) _ _ _ _ _) := fun e => do
  unless e.getAppNumArgs == 6 do return .continue
  onReturn e 4 ``ok_bind

/-- A handled computation that returns continues with the value. -/
simproc ↓ tryWithReturned (tryWith _ _ _) := fun e => do
  unless e.getAppNumArgs == 5 do return .continue
  onReturn e 2 ``tryWith_ok

/-- A guard whose computation returns selects its branch from the value. -/
simproc ↓ guardReturned (guard _ _ _) := fun e => do
  unless e.getAppNumArgs == 4 do return .continue
  onReturn e 1 ``guard_ok

end Simplification

end Lynx.Except

namespace Lynx.Term.Bitstring

section Termination
open Lean Meta Elab Tactic

/-- Facts about the measure left by a successful extraction. -/
private meta def extractionFacts : Array Name := #[
  ``matchInteger_sizeOf_integer,
  ``matchInteger_sizeOf_le,
  ``matchBinary_sizeOf_integer,
  ``matchBinary_sizeOf_le,
  ``matchFloat_sizeOf,
  ``matchUtf8_sizeOf,
  ``matchUtf16_sizeOf,
  ``matchUtf32_sizeOf]

/-- Facts about extractions whose variable size was checked to be nonzero. -/
private meta def nonzeroFacts : Array Name := #[
  ``matchInteger_sizeOf_nonzero,
  ``matchBinary_sizeOf_nonzero,
  ``matchFloat_sizeOf_nonzero]

/-- Record the measure left by every extraction equation in context. Local
definitions are unfolded in the goal and the new facts, so `omega` relates
the extracted bits to the recursive arguments. -/
elab "lynx_extraction_facts" : tactic => do
  liftMetaTactic fun goal => goal.withContext do
    let mut goal ← goal.change (← zetaReduce (← instantiateMVars (← goal.getType)))
    let declarations := (← getLCtx).foldl (init := #[]) fun acc declaration =>
      if declaration.isImplementationDetail then acc else acc.push declaration
    let assertFact (goal : MVarId) (proof : Expr) : MetaM MVarId := do
      let fact ← zetaReduce (← instantiateMVars (← inferType proof))
      let (_, next) ← (← goal.assert `consumed fact proof).intro1P
      return next
    for declaration in declarations do
      unless (← instantiateMVars declaration.type).isAppOfArity ``Eq 3 do continue
      for lemma in extractionFacts do
        try goal ← assertFact goal (← mkAppM lemma #[declaration.toExpr]) catch _ => pure ()
      for check in declarations do
        unless (← instantiateMVars check.type).isAppOfArity ``Not 1 do continue
        for lemma in nonzeroFacts do
          try goal ← assertFact goal (← mkAppM lemma #[check.toExpr, declaration.toExpr])
          catch _ => pure ()
    return [goal]

macro_rules | `(tactic| decreasing_trivial) => `(tactic| (lynx_extraction_facts; omega))

end Termination

end Lynx.Term.Bitstring

namespace Lynx.Concurrent

section Counterexample
open Lean Meta Elab Tactic

/-- Fail with a run that `Lynx.Concurrent.check` rejects, when there is one,
and otherwise leave the goal unchanged for a tactic such as `cbv` to prove. The
goal must be `Lynx.Concurrent.check accept depth config = true` for a program
returning a term, closed except for natural numbers, such as a law's call depth,
which the search takes to be zero, and the time elapsed when timers are canceled,
which it takes to be none and then enough for every canceled timer to have none left. The search runs the program in Lean's interpreter,
which finds a failing run much faster than the kernel evaluates `check`. It
is only a diagnostic: the kernel never relies on it. -/
syntax (name := counterexampleTactic) "lynx_counterexample" : tactic

@[tactic counterexampleTactic] public meta def evalCounterexample : Tactic := fun _ => do
  let goal ← instantiateMVars (← getMainTarget)
  let expected := "lynx_counterexample expects a goal `Lynx.Concurrent.check accept depth config = true`"
  let some (_, check, _) := goal.eq? | throwError expected
  -- Laws hold from some call depth on, so the search runs at the smallest
  -- depth, taking every natural number in the check to be zero.
  let naturals ← (collectFVars {} check).fvarIds.filterM fun fvar =>
    return (← fvar.getType).isConstOf ``Nat
  let check := check.replaceFVars (naturals.map mkFVar) (naturals.map fun _ => mkNatLit 0)
  -- The time elapsed when timers are canceled can be any. The search tries
  -- none elapsed, and enough elapsed that every canceled timer has none left.
  let elapsedType ← mkArrow (mkConst ``Lynx.PID) (← mkArrow (mkConst ``Nat) (mkConst ``Nat))
  let elapsed ← (collectFVars {} check).fvarIds.filterM fun fvar => do
    isDefEq (← fvar.getType) elapsedType
  let constant (milliseconds : Nat) : Expr :=
    mkLambda `_ .default (mkConst ``Lynx.PID) (mkLambda `_ .default (mkConst ``Nat)
      (mkNatLit milliseconds))
  let attempts := if elapsed.isEmpty then [0] else [0, 4294967295]
  for milliseconds in attempts do
    let check := check.replaceFVars (elapsed.map mkFVar)
      (elapsed.map fun _ => constant milliseconds)
    let_expr Lynx.Concurrent.check result accept depth config := check | throwError expected
    unless ← isDefEq result (mkConst ``Lynx.Term) do
      throwError "lynx_counterexample expects a program returning a term, not {result}"
    let fvars := (collectFVars {} check).fvarIds
    unless fvars.isEmpty do
      let names ← fvars.mapM (·.getUserName)
      throwError "lynx_counterexample runs closed programs, but this one depends on {names.toList}"
    if check.hasMVar then
      throwError "lynx_counterexample runs closed programs, but this one has metavariables"
    let name ← mkAuxDeclName `_lynx_counterexample
    let report := mkApp3 (mkConst ``Lynx.Concurrent.report) accept depth config
    let found ← withoutModifyingEnv do
      addAndCompile (.defnDecl {
        name, levelParams := [], type := ← mkAppM ``Option #[mkConst ``String], value := report
        hints := .opaque, safety := .safe })
      -- The program is ordinary code, imported for evaluation by the runner.
      try unsafe evalConst (Option String) name (checkMeta := false)
      catch error => throwError "lynx_counterexample could not run the program: {error.toMessageData}"
    if let some message := found then
      let mut names ← naturals.mapM fun fvar => return s!"{← fvar.getUserName} = 0"
      names := names ++ (← elapsed.mapM fun fvar =>
        return s!"{← fvar.getUserName} = fun _ _ => {milliseconds}")
      if names.isEmpty then throwError message
      throwError "{message}\nwhere {", ".intercalate names.toList}"

end Counterexample

section Kernel
open Lean Meta Elab Tactic

/-- Prove a goal `lhs = true` by kernel evaluation, such as
`Lynx.Concurrent.check accept depth config = true`. The goal's locals are
abstracted into an auxiliary theorem whose proof is `Eq.refl true`, so the
kernel evaluates `lhs` with them free, as it can a law's call depth, or the
time elapsed when timers are canceled, when evaluation does not need their
values. The elaborator does not evaluate it, and no axiom is added. -/
syntax (name := kernelTactic) "lynx_kernel" : tactic

@[tactic kernelTactic] public meta def evalKernel : Tactic := fun _ => do
  let goal ← getMainGoal
  goal.withContext do
    let type ← instantiateMVars (← goal.getType)
    let expected := "lynx_kernel expects a goal `lhs = true`"
    let some (_, _, rhs) := type.eq? | throwError expected
    unless rhs.isConstOf ``Bool.true do throwError expected
    if type.hasMVar then throwError "lynx_kernel expects a goal without metavariables"
    let locals ← (← getLCtx).foldlM (init := #[]) fun locals decl =>
      return if decl.isImplementationDetail then locals else locals.push decl.toExpr
    let closedType ← mkForallFVars locals type
    let closedValue ← mkLambdaFVars locals
      (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
    let levelParams := (collectLevelParams {} closedType).params.toList
    let name ← mkAuxDeclName `_lynx_kernel
    addDecl (.thmDecl { name, levelParams, type := closedType, value := closedValue })
    goal.assign (mkAppN (mkConst name (levelParams.map mkLevelParam)) locals)
    replaceMainGoal []

end Kernel

end Lynx.Concurrent
