module

public meta import Lean
public import Lynx.Term.Bitstring.Matching
public import Lynx.Term.Except

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
