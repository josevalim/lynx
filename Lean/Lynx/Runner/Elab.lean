module

public meta import Lean
public import Lynx.Term.Bitstring.Matching

/-! Elaborators for translated programs.

Elaborators depend on Lean's elaborator, so they live here rather than in `Lynx`.
The runner imports this module alongside `Lynx` for translated code, which keeps
the library itself free of Lean's elaborator, for example in `lake check` exports.

## Termination

Recursion over the bits left by an extraction, such as bitstring generators,
decreases `sizeOf` by the consumed bits. Bitstring extractions continue through
`extract`, whose well-founded preprocessing passes the extraction's
equation to its continuation. Lean's default `decreasing_tactic` tries
`decreasing_trivial`, which this extends. -/

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
