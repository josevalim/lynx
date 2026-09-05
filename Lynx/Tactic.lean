import Lean
import Lynx.Modules.Enum

/-!
# How the Lynx tactic works

`lynx_verify` proves translated Elixir contracts using the executable Lean
definitions themselves. It does not require a semantic theorem for every
function, nor an annotation on every translated definition.

## Contract generation

`Satisfies function expects ensures` is deliberately a conjunction:

```lean
Covered expects ∧
  ∀ input, Accepted (expects input) →
    ∃ result, function input = .value result ∧
      Accepted (ensures input result)
```

`Property expects expression` has the same `Covered expects` conjunct. Thus a
proof can never succeed merely because the expectation accepts no inputs.
`Accepted outcome` means exactly `outcome = .value Term.true`; false, non-boolean
values, and exceptions are not accepted.

For a single contract or property, `lynx_vcgen` separates coverage from behavior,
using the goal tags `coverage` and `ensures` (or `property`). It unfolds the
contract wrappers, introduces behavioral inputs and assumptions, and unpacks
structure arguments, including tuples. A `WithSourceLabel` whose file and line
reduce to literals supplies source information for the goal tags.
`EnsuresClauses` shares one coverage condition across its labeled guarantees.
Generation may close trivial wrapper goals such as `True`, but it does not run
the solver or normalize executable expectations. `lynx_verify` generates the
same conditions and invokes the solver on each.

If automatic witness search cannot establish coverage, `lynx_verify` reports:

```text
lynx: could not prove that `expects` accepts any input; it may be empty or unsupported by automatic coverage
```

Failed bounded witness search does not prove that the expectation is empty: an
accepted value may lie outside the candidate set. No separate emptiness search
is needed for soundness because the required `Covered` proof remains unsolved.
An interactive proof may use `lynx_vcgen` and provide the witness directly.

## Definition discovery and normalization

For symbolic proof search, the solver gathers constants used by the goal
and local hypotheses. It follows definitions whose result is `Outcome _`, then
builds one local simplification context from those executable bodies. This is
why ordinary translated functions need no registration attribute or separate
semantics file. Library-level, kernel-proved `@[simp]` rules supplement the
executable bodies, including `Outcome` reductions and the `andalso` acceptance
shortcut; translated functions themselves remain annotation-free. The library
uses the `_spec` suffix for these theorems. Their statements and `@[simp]`
attributes drive rewriting; that naming convention is not a discovery rule.

Normalization makes one ordered pass over non-quantified hypotheses, starting
with expectation-derived constraints, and then simplifies the target. Each
updated fact immediately replaces its old rewrite rule, so duplicate facts
cannot both disappear by simplifying each other to `True`. This normalization
pass neither rewrites quantified hypotheses nor adds them as local simp rules;
separate guarded application handles induction hypotheses and summaries.
Rejected input branches usually close before the implementation's possible
results are explored.

## Propagating acceptance requirements

An expectation is accepted only when its final outcome is `.value Term.true`.
The solver can propagate this requirement inward through an expression using
proved equivalences, instead of first enumerating every operational outcome.
For `andalso`, the logical view is:

```lean
Accepted (Modules.Erlang.andalso left right) ↔
  Accepted left ∧ Accepted (right ())
```

`Modules.Erlang.andalso_spec` proves this fact directly from the executable
definition. Its statement uses the unfolded equality with
`.value (.atom "true")`, so simp can match it after `Accepted`, `Term.true`,
and executable wrappers have unfolded. In a hypothesis, the resulting
conjunction supplies facts about both operands; in a target, it expresses the
requirements for acceptance. Nested conjunctions can be exposed the same way.
This is an equivalence, not an assumption that either operand succeeds.

The tactic deliberately adds `andalso`'s executable equations to the simp
context instead of unfolding its body eagerly. Known outcomes still reduce,
including short-circuiting and exceptions, while an unknown computation stays
recognizable by the acceptance shortcut. Eager expansion into a match hides
that opportunity; the benchmarks showed slower verification with that strategy.

This optimization currently happens in the solver's simplification passes. `lynx_vcgen`
still emits conditions about the original executable expressions; it does not
compile expectations into a separate logical representation. The same rewrite
can apply wherever an acceptance condition occurs, including coverage,
guarantees, properties, and recursive-call premises.

Only the final accepted outcome is restricted to `true`. Intermediate false,
non-boolean, and exceptional outcomes retain their executable meaning. Further
acceptance shortcuts need proved equivalences: an `orelse` acceptance rule, for
example, would have to distinguish a left operand returning `false` from one
raising an exception. There is no `orelse` implementation or shortcut here yet.
Coverage still requires an actual input satisfying the executable expectation.

## Bounded search

`solveGoal` first attempts coverage, then builds a solver context if needed.
For a non-existential target it attempts summary synthesis before the main
search. Each main search call follows this order; structural changes and
successful hypothesis applications recurse with less fuel on the resulting
goals:

1. Introduce binders and solve a `Covered` goal by testing a small set of
   concrete `Term`, tuple, unit, or structure values. First try reflexivity on
   every candidate, using definitional evaluation without a simp context; if
   none succeeds, fall back to the guard prover. A candidate is accepted only
   after proving the real executable expectation; the candidate list is not
   treated as a model of the domain.
2. Destructure conjunctions, existentials, and products in hypotheses. If none
   is available, normalize hypotheses and the target, then try destructuring
   again.
3. Split eligible hypothesis matches before exploring returned values,
   protecting recorded input variables so they remain available for induction.
4. Specialize a synthesized summary when applicable, or apply a hypothesis with
   a propositional premise. Each application must first prove its premise in a
   separate goal. Premise preparation attempts to clear quantified hypotheses
   and unrelated assumptions, retaining any required by local dependencies.
5. Try assumptions, reflexivity, `omega`, and `grind` with case splitting
   disabled.
6. Induct on a recorded `Term` input used as the structural argument of a
   discovered recursive definition. Simplify branch targets and try to remove
   induction hypotheses irrelevant to remaining recursive calls. More than one
   independent input may be inducted.
7. Generalize and split one shared monadic computation, retaining an equation
   for its outcome. This avoids duplicating nested bind continuations before
   its `Outcome.value`/`Outcome.raised` result is known.
8. Try remaining hypothesis matches, then split a target match or conditional.

The main search and independent summary proofs start with fuel 24. The smaller
guard prover uses simplification, leaf solvers, destructuring, and splitting;
it does not perform induction or synthesize summaries. Coverage fallback uses
guard fuel 12, and hypothesis applications use 8. Coverage candidates have a
construction depth limit of 3: products combine candidates, while structures
use the first available candidate for each field.

These searches are bounded and incomplete. Failure to close a goal is not
interpreted as a counterexample; `lynx_solve` leaves residual goals available
for an explicit invariant or ordinary tactic. `set_option trace.lynx true`
shows search goals and fuel, coverage failures, summary attempts, and timings.

## Relational properties

Properties such as `sum(l) + sum(r) == sum(l ++ r)` need information about
recursive calls on values other than a direct structural child. The solver
therefore attempts a narrow summary synthesis step:

1. Find discovered recursive functions of type `Term → Outcome Term`.
2. Find candidate input domains inside existing `Accepted` hypotheses, looking
   through executable wrappers with bounded traversal.
3. Look for a single candidate `Term` constructor in normal returns from the
   function body and the executable callees it follows.
4. Construct a normal-return proposition and prove it in a fresh context using
   the same bounded search.
5. Add the summary only if that independent proof closed completely.

The summary is a proved local theorem, never an assumption or a reuse of
another application contract. After induction, the solver may specialize it
for a unary recursive call in the target when an existing hypothesis contains
the corresponding domain constraint. It still proves that constraint before
using the summary; it does not invent a domain for arbitrary intermediate
results. Current synthesis handles unary functions with a uniform candidate
result constructor when bounded search can prove the conjecture. It is not
general invariant discovery.

## Trust boundary

The tactic constructs proof terms that Lean's kernel checks against the stated
theorem. Definition discovery, witness selection, branch ordering, and summary
conjecture need not themselves be trusted for logical correctness: a wrong
guess still needs a valid proof. Bugs can cause failure, excessive search, or
a proof term rejected by the kernel.

This guarantee assumes the correctness of Lean's kernel and excludes reliance
on `sorry` or additional untrusted axioms. The proof-audit tests inspect
representative generated proofs, accepting only `propext`, `Classical.choice`,
and `Quot.sound` among their axioms; this is not a per-invocation audit of every
use of the tactic. Kernel checking establishes the stated Lean contract, not
that the term model, translated operations, or contract express the intended
Erlang behavior. Those definitions and the translation still require review.
-/

open Lean Meta Elab Tactic

namespace Lynx.Tactic

initialize registerTraceClass `lynx

private def allGoals (action : TacticM Unit) : TacticM Unit := do
  let goals ← getGoals
  let mut remaining := []
  for goal in goals do
    unless ← goal.isAssigned do
      setGoals [goal]
      action
      remaining := remaining ++ (← getGoals)
  setGoals remaining

private def replaceBranches (branches : List MVarId) : TacticM Unit := do
  let source ← (← getGoals).head!.getTag
  unless source.isAnonymous do
    for branch in branches do
      let tag ← branch.getTag
      unless source.isPrefixOf tag do branch.setTag (source ++ tag)
  replaceMainGoal branches

private structure Solver where
  context : Simp.Context
  simprocs : Simp.SimprocsArray
  recursive : Array Name
  majors : NameMap Nat
  inputs : Array FVarId
  inducted : Bool := false

/-- Discover executable definitions by their result type, following their calls.
Their bodies supply reduction rules alongside registered library simp theorems;
translated definitions need no separate semantic theorem. -/
private def mkSolver : TacticM Solver := withMainContext do
  let mut pending := (← getMainTarget).getUsedConstants
  let mut inputs := #[]
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      pending := pending ++ decl.type.getUsedConstants
      if decl.type.isConstOf ``Lynx.Term then inputs := inputs.push decl.fvarId
  let mut seen : NameSet := {}
  let mut definitions : Array (TSyntax `ident) := #[]
  let mut recursive := #[]
  let mut majors : NameMap Nat := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let .defnInfo info ← getConstInfo name | continue
    let executable ← forallTelescopeReducing info.type fun _ result =>
      pure (result.isAppOf ``Outcome)
    unless executable do continue
    if name != ``Modules.Erlang.andalso then
      definitions := definitions.push (mkIdent name)
    else if let some equations ← getEqnsFor? name then
      -- Unfolding the body here would hide `andalso` from its logical rule.
      -- Equations still handle short-circuiting, exceptions, and bad booleans.
      definitions := definitions ++ equations.map mkIdent
    if ← isRecursiveDefinition name then
      recursive := recursive.push name
      if let some index ← getStructuralRecArgPos? name then
        majors := majors.insert name index
    pending := pending ++ info.value.getUsedConstants
  let simpSyntax ← `(tactic| simp_all (config := { failIfUnchanged := false })
    [Accepted, Term.true, Term.false,
    Pure.pure, $[$definitions:ident],*])
  let result ← mkSimpContext simpSyntax (eraseLocal := true) (kind := .simpAll)
  return ⟨result.ctx, result.simprocs, recursive, majors, inputs, false⟩

/-- One forward pass; search revisits normalization after structural progress.
Do not repeatedly traverse quantified recursive proofs as `simpAll` does. -/
private def normalize (solver : Solver) : TacticM Bool := do
  let start ← IO.monoMsNow
  let mut goal ← getMainGoal
  let (hypotheses, context) ← goal.withContext do
    let hypotheses ← (← getPropHyps).filterM fun h => return !(← h.getType).isForall
    let mut context := solver.context
    for h in hypotheses do
      context := context.setSimpTheorems (← context.simpTheorems.addTheorem
        (.fvar h) (mkFVar h) (config := context.indexConfig))
    let constraints ← hypotheses.filterM fun h => do
      let decl ← h.getDecl
      return !decl.userName.toString.startsWith "recursive_result" &&
        (decl.type.isAppOf ``Accepted ||
          (decl.type.isAppOf ``Eq && decl.type.getAppArgs[2]!.isAppOf ``Outcome.value))
    return (constraints ++ hypotheses.filter (fun h => !constraints.contains h), context)
  let mut context := context
  for h in hypotheses do
    -- Replace rules immediately: simplifying all facts against the original
    -- set could turn both copies of a duplicate hypothesis into `True`.
    context := context.setSimpTheorems (context.simpTheorems.eraseTheorem (.fvar h))
    let (result, _) ← simpLocalDecl goal h context solver.simprocs
    let some (h, next) := result | setGoals []; return true
    goal := next
    let type ← goal.withContext h.getType
    if type.isTrue then
      goal ← goal.tryClear h
    else
      context ← goal.withContext do
        return context.setSimpTheorems (← context.simpTheorems.addTheorem
          (.fvar h) (mkFVar h) (config := context.indexConfig))
  let (result, _) ← simpTarget goal context solver.simprocs
  trace[lynx] "normalize: {(← IO.monoMsNow) - start}ms"
  replaceMainGoal result.toList
  return result.isNone

private def closeLeaf : TacticM Bool := do
  let saved ← saveState
  try
    evalTactic (← `(tactic| first | assumption | rfl | omega |
      grind (splits := 0) [Accepted, Term.true, Term.false]))
    return true
  catch _ =>
    saved.restore
    return false

private def destructFacts : TacticM Bool := withMainContext do
  let goal ← getMainGoal
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      let type ← whnf decl.type
      if type.isAppOf ``Exists || type.isAppOf ``And || type.isAppOf ``Prod then
        let branches ← goal.cases decl.fvarId
        replaceBranches (branches.toList.map (·.mvarId))
        return true
  return false

/-- Split match-bearing hypotheses, including compound computations. Early calls
protect prospective induction inputs; later calls prioritize recursive results. -/
private def splitHypothesis (protectedInputs : Array FVarId := #[])
    (constraintsOnly : Bool := false) : TacticM Bool := withMainContext do
  let goal ← getMainGoal
  let mut declarations := #[]
  for decl in ← getLCtx do declarations := declarations.push decl
  if !constraintsOnly then
    declarations := declarations.filter (fun d => d.userName.toString.startsWith "recursive_result") ++
      declarations.filter (fun d => !d.userName.toString.startsWith "recursive_result")
  for decl in declarations do
    unless decl.isImplementationDetail || decl.type.isForall do
      if constraintsOnly && decl.userName.toString.startsWith "recursive_result" then continue
      let discriminants ← IO.mkRef (#[] : Array FVarId)
      decl.type.forEach fun e => do
        if let some matcher ← matchMatcherApp? e then
          for discr in matcher.discrs do
            if discr.isFVar && !protectedInputs.contains discr.fvarId! then
              discriminants.modify (·.push discr.fvarId!)
      for discr in ← discriminants.get do
        let branches ← goal.cases discr
        replaceBranches (branches.toList.map (·.mvarId))
        return true
      if let some candidate ← findSplit? decl.type then
        if let some matcher ← matchMatcherApp? candidate then
          if matcher.discrs.any (fun d => protectedInputs.any d.containsFVar) then
            continue
      if let some branches ← splitLocalDecl? goal decl.fvarId then
        replaceBranches branches
        return true
  return false

private def inductInput (solver : Solver) : TacticM (Option Solver) := withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  for input in solver.inputs do
    unless (← getLCtx).contains input do continue
    if (target.find? fun e =>
        match solver.majors.find? (e.getAppFn.constName?.getD .anonymous) with
        | some index => e.getAppArgs[index]? == some (mkFVar input)
        | none => false).isSome then
      let branches ← goal.induction input ``Lynx.Term.rec
      let mut remaining := []
      for branch in branches do
        let (simplified, _) ← simpTarget branch.mvarId solver.context solver.simprocs
        let some next := simplified | continue
        let next ← next.withContext do
          let mut next := next
          let target ← next.getType
          let children ← branch.fields.filterM fun field =>
            return (← inferType field).isConstOf ``Term
          for field in branch.fields do
            let type ← inferType field
            unless ← isProp type do continue
            let needed := children.any fun child =>
              type.containsFVar child.fvarId! && (target.find? fun e =>
                match solver.majors.find? (e.getAppFn.constName?.getD .anonymous) with
                | some index => e.getAppArgs[index]? == some child
                | none => false).isSome
            unless needed do next ← next.tryClear field.fvarId!
          return next
        remaining := remaining ++ [next]
      replaceBranches remaining
      return some { solver with inputs := solver.inputs.filter (· != input), inducted := true }
  return none

/-- Inspect one shared computation at a time. Keeping binds intact until this
point avoids expanding all continuations into nested matches during simp. -/
private def splitComputation : TacticM Bool := withMainContext do
  let goal ← getMainGoal
  let mut expressions := #[]
  for decl in ← getLCtx do
    if !decl.isImplementationDetail && !decl.type.isForall then
      expressions := expressions.push decl.type
  expressions := expressions.push (← goal.getType)
  for expression in expressions do
    let candidates ← IO.mkRef (#[] : Array Expr)
    expression.forEach fun e => do
      if e.isAppOf ``Bind.bind then
        let args := e.getAppArgs
        if args.size >= 2 then
          let computation := args[args.size - 2]!
          unless computation.hasLooseBVars do
            if !computation.isAppOf ``Bind.bind && !computation.isAppOf ``Outcome.value &&
                !computation.isAppOf ``Outcome.raised && (← inferType computation).isAppOf ``Outcome then
              candidates.modify (·.push computation)
    for computation in ← candidates.get do
      let saved ← saveState
      try
        let (_, variables, next) ← goal.generalizeHyp
          #[{ expr := computation, xName? := some `outcome, hName? := some `evaluated }]
          (← getPropHyps)
        let branches ← next.cases variables[0]!
        replaceBranches (branches.toList.map (·.mvarId))
        return true
      catch _ => saved.restore
  return false

/-- Prove coverage or call premises by bounded simplification and splitting,
without induction or summary synthesis. -/
private partial def proveGuard (solver : Solver) (fuel : Nat) : TacticM Unit := do
  if fuel == 0 then return
  match (← simpTargetStar (← getMainGoal) solver.context solver.simprocs).1 with
  | .closed => setGoals []; return
  | .modified goal => setGoals [goal]
  | .noChange => pure ()
  if ← normalize solver then return
  if ← closeLeaf then return
  if ← destructFacts then
    allGoals (proveGuard solver (fuel - 1))
  else if let some branches ← splitTarget? (← getMainGoal) then
    replaceBranches branches
    allGoals (proveGuard solver (fuel - 1))
  else if ← splitComputation then
    allGoals (proveGuard solver (fuel - 1))
  else if ← splitHypothesis then
    allGoals (proveGuard solver (fuel - 1))

/-- Slice premise assumptions by shared free-variable dependencies. Attempt to
clear quantified and unrelated hypotheses; keep declarations needed by others. -/
private def guardGoal (premise : Expr) : TacticM Expr := do
  let proof ← mkFreshExprSyntheticOpaqueMVar premise
  let mut goal := proof.mvarId!
  let mut relevant := (Lean.collectFVars {} premise).fvarIds
  let context ← getLCtx
  for _ in [:context.size] do
    let mut changed := false
    for decl in context do
      if decl.type.isForall || !(← isProp decl.type) then continue
      let vars := (Lean.collectFVars {} decl.type).fvarIds
      if vars.any relevant.contains then
        for v in vars do
          unless relevant.contains v do
            relevant := relevant.push v
            changed := true
    unless changed do break
  for decl in context do
    if ← isProp decl.type then
      let vars := (Lean.collectFVars {} decl.type).fvarIds
      if decl.type.isForall || (!vars.isEmpty && !vars.any relevant.contains) then
        goal ← goal.tryClear decl.fvarId
  setGoals [goal]
  return proof

/-- Small concrete values used to establish that a generated expectation has
an accepted input. This is witness search, not an approximation of the domain:
the selected candidate still has to prove the real executable expectation. -/
private partial def coverageCandidates (type : Expr) (depth : Nat := 3) : TacticM (Array Expr) := do
  if depth == 0 then return #[]
  let type ← whnf type
  if type.isConstOf ``Term then
    return #[
      ← elabTerm (← `(Term.integer 0)) (some type),
      ← elabTerm (← `(Term.nil)) (some type),
      ← elabTerm (← `(Term.atom "")) (some type),
      ← elabTerm (← `(Term.atom "true")) (some type),
      ← elabTerm (← `(Term.cons (Term.integer 0) Term.nil)) (some type),
      ← elabTerm (← `(Term.cons (Term.atom "") Term.nil)) (some type)]
  if type.isAppOf ``Prod then
    let args := type.getAppArgs
    let left ← coverageCandidates args[0]! (depth - 1)
    let right ← coverageCandidates args[1]! (depth - 1)
    let mut result := #[]
    for l in left do
      for r in right do result := result.push (← mkAppM ``Prod.mk #[l, r])
    return result
  if type.isConstOf ``Unit then return #[mkConst ``Unit.unit]
  let some name := type.getAppFn.constName? | return #[]
  let env ← getEnv
  let some _ := getStructureInfo? env name | return #[]
  let ctor := getStructureCtor env name
  let constructor ← mkConstWithFreshMVarLevels ctor.name
  let (args, _, result) ← forallMetaTelescopeReducing (← inferType constructor)
  unless ← isDefEq result type do return #[]
  for index in [ctor.numParams : ctor.numParams + ctor.numFields] do
    let field := args[index]!
    unless field.isMVar do return #[]
    let candidates ← coverageCandidates (← inferType field) (depth - 1)
    let some candidate := candidates[0]? | return #[]
    field.mvarId!.assign candidate
  return #[← instantiateMVars (mkAppN constructor args)]

private partial def nameHasComponent (name : Name) (component : String) : Bool :=
  match name with
  | .anonymous => false
  | .str parent value => value == component || nameHasComponent parent component
  | .num parent _ => nameHasComponent parent component

private def hasCoverageTag (goal : MVarId) : MetaM Bool := do
  return nameHasComponent (← goal.getTag) "coverage"

/-- Concrete coverage normally needs only evaluation. Build a simplification
context lazily, retaining the guard prover for expectations using local facts. -/
private def solveCoverage (solver? : Option Solver := none) : TacticM Bool := withMainContext do
  let goal ← getMainGoal
  let rawTarget ← goal.getType
  unless rawTarget.isAppOf ``Covered || (← hasCoverageTag goal) do return false
  let target ← withTransparency .all <| whnf rawTarget
  unless target.isAppOf ``Exists do return false
  let args := target.getAppArgs
  let candidates ← coverageCandidates args[0]!
  for reduceOnly in #[true, false] do
    let solver? ← if reduceOnly then pure none else some <$> solver?.getDM mkSolver
    for candidate in candidates do
      let saved ← saveState
      try
        let proposition ← whnf (mkApp args[1]! candidate)
        let proof ← mkFreshExprSyntheticOpaqueMVar proposition
        setGoals [proof.mvarId!]
        if let some solver := solver? then
          proveGuard solver 12
        else
          proof.mvarId!.refl
          setGoals []
        unless (← getGoals).isEmpty do
          saved.restore
          continue
        let .sort level ← whnf (← inferType args[0]!)
          | throwError "coverage domain is not a sort"
        let intro := mkConst ``Exists.intro [level]
        goal.assign (mkAppN intro #[args[0]!, args[1]!, candidate, ← instantiateMVars proof])
        setGoals []
        return true
      catch error =>
        trace[lynx] "coverage candidate {candidate} failed: {error.toMessageData}"
        saved.restore
  return false

private def applyHypothesis (solver : Solver) : TacticM Bool := withMainContext do
  let goal ← getMainGoal
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      let type ← whnf decl.type
      let .forallE _ premise _ _ := type | continue
      unless ← isProp premise do continue
      let saved ← saveState
      try
        let proof ← guardGoal premise
        proveGuard solver 8
        unless (← getGoals).isEmpty do
          saved.restore
          continue
        let value := mkApp decl.toExpr (← instantiateMVars proof)
        let resultType ← inferType value
        let next ← goal.assert (← mkFreshUserName `recursive_result) resultType value
        let (_, next) ← next.intro1
        let next ← next.tryClear decl.fvarId
        setGoals [next]
        return true
      catch _ => saved.restore
  return false

private def applySummary (solver : Solver) : TacticM Bool := withMainContext do
  unless solver.inducted do return false
  let goal ← getMainGoal
  let target ← goal.getType
  for decl in ← getLCtx do
    unless decl.userName.toString.startsWith "normal_return" do continue
    let .forallE _ domain _ _ := decl.type | continue
    unless domain.isConstOf ``Term do continue
    let calls ← IO.mkRef (#[] : Array Expr)
    target.forEach fun e => do
      if !e.hasLooseBVars && e.isApp && solver.recursive.contains (e.getAppFn.constName?.getD .anonymous) then
        calls.modify (·.push e)
    for call in ← calls.get do
      let args := call.getAppArgs
      unless args.size == 1 do continue
      let saved ← saveState
      try
        let partialProof := mkApp decl.toExpr args[0]!
        let type ← whnf (← inferType partialProof)
        let .forallE _ premise body _ := type | continue
        -- Only specialize a summary for the computation actually being inspected.
        unless body.getUsedConstants.contains (call.getAppFn.constName?.getD .anonymous) do continue
        -- A summary is useful only where an expectation already constrains
        -- this argument. Do not search for a new invariant on an arbitrary
        -- intermediate result (for example, the result of concatenation).
        let constraint := if premise.isAppOf ``Accepted then premise.getAppArgs[0]!
          else if premise.isAppOf ``Eq then premise.getAppArgs[1]! else premise
        unless (← getLCtx).any (fun h => !h.type.isForall &&
            (h.type.find? (· == constraint)).isSome) do continue
        let proof ← guardGoal premise
        proveGuard solver 8
        unless (← getGoals).isEmpty do
          saved.restore
          continue
        let value := mkApp partialProof (← instantiateMVars proof)
        let resultType ← inferType value
        let next ← goal.assert (← mkFreshUserName `call_result) resultType value
        let (_, next) ← next.intro1
        setGoals [next]
        return true
      catch _ => saved.restore
  return false

/-- Normalize constraints and check guarded applications before induction or
outcome splitting. Independent inputs can each receive their own induction. -/
private partial def search (solver : Solver) (fuel : Nat) : TacticM Unit := do
  if fuel == 0 then return
  trace[lynx] "search ({fuel}): {← getMainGoal}"
  let (_, goal) ← (← getMainGoal).intros
  replaceMainGoal [goal]
  if ← solveCoverage (some solver) then return
  if ← destructFacts then
    allGoals (search solver (fuel - 1))
    return
  if ← normalize solver then return
  if ← destructFacts then
    allGoals (search solver (fuel - 1))
    return
  if ← splitHypothesis solver.inputs true then
    allGoals (search solver (fuel - 1))
    return
  if ← applySummary solver then
    search solver (fuel - 1)
    return
  if ← applyHypothesis solver then
    search solver (fuel - 1)
    return
  if ← closeLeaf then return
  if let some solver ← inductInput solver then
    allGoals (search solver (fuel - 1))
    return
  if ← splitComputation then
    allGoals (search solver (fuel - 1))
    return
  if ← splitHypothesis then
    allGoals (search solver (fuel - 1))
    return
  if let some branches ← splitTarget? (← getMainGoal) then
    replaceBranches branches
    allGoals (search solver (fuel - 1))

/-- Candidate domains are executable predicates already present in the expects
clause. Looking inside wrappers does not assume that any candidate is accepted. -/
private partial def collectDomains (expression : Expr) (fuel : Nat) : MetaM (Array Expr) := do
  if fuel == 0 then return #[]
  let mut result := #[]
  if expression.isApp && !expression.hasLooseBVars then
    let args := expression.getAppArgs
    if (← whnf args.back!).isFVar && (← inferType args.back!).isConstOf ``Term then
      let fn := mkAppN expression.getAppFn args.pop
      if (← inferType expression).isAppOf ``Outcome then result := result.push fn
    if let .const name _ := expression.getAppFn then
      if !(← isRecursiveDefinition name) then
        if let some unfolded ← unfoldDefinition? expression then
          result := result ++ (← collectDomains unfolded (fuel - 1))
  match expression with
  | .app f a =>
    result := result ++ (← collectDomains f (fuel - 1)) ++ (← collectDomains a (fuel - 1))
  | .lam _ _ body _ =>
    if !body.hasLooseBVars then result := result ++ (← collectDomains body (fuel - 1))
  | _ => pure ()
  return result

/-- Infer a uniform constructor of normal returns from executable bodies. This
is only a conjecture: the resulting summary must still be proved independently. -/
private def returnConstructor (function : Name) : MetaM (Option Name) := do
  let mut pending := #[function]
  let mut seen : NameSet := {}
  let constructors ← IO.mkRef ({} : NameSet)
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let .defnInfo info ← getConstInfo name | continue
    info.value.forEach fun e => do
      if e.isAppOfArity ``Outcome.value 2 then
        let returned := e.getAppArgs[1]!
        if let .const ctor _ := returned.getAppFn then
          if let .ctorInfo ci ← getConstInfo ctor then
            if ci.induct == ``Term then constructors.modify (·.insert ctor)
    for callee in info.value.getUsedConstants do
      if callee == function then continue
      let .defnInfo calleeInfo ← getConstInfo callee | continue
      if ← forallTelescopeReducing calleeInfo.type fun _ result => pure (result.isAppOf ``Outcome) then
        pending := pending.push callee
  let names := (← constructors.get).toArray
  return if names.size == 1 then some names[0]! else none

private def synthesizeSummaries (solver : Solver) : TacticM Unit := withMainContext do
  let mut domains := #[]
  for decl in ← getLCtx do
    if decl.type.isAppOf ``Accepted then
      domains := domains ++ (← collectDomains decl.type.getAppArgs[0]! 16)
  trace[lynx] "summary domains: {domains}; recursive: {solver.recursive}"
  domains := domains.filter (fun d => solver.recursive.contains (d.getAppFn.constName?.getD .anonymous)) ++
    domains.filter (fun d => !solver.recursive.contains (d.getAppFn.constName?.getD .anonymous))
  for function in solver.recursive do
    let info ← getConstInfo function
    unless ← isDefEq info.type (← elabTerm (← `(Term → Outcome Term)) none) do continue
    let some constructor ← returnConstructor function | continue
    trace[lynx] "summary constructor: {function} -> {constructor}"
    let mut seen : ExprSet := {}
    for domain in domains do
      if seen.contains domain then continue
      seen := seen.insert domain
      let goal ← getMainGoal
      let saved ← saveState
      try
        let proposition ← withLocalDeclD `input (mkConst ``Term) fun input => do
          let accepted ← mkAppM ``Accepted #[mkApp domain input]
          let result ← forallTelescope (← inferType (mkConst constructor)) fun fields _ => do
            let value ← mkAppM ``Outcome.value #[mkAppN (mkConst constructor) fields]
            let mut equation ← mkEq (mkApp (mkConst function) input) value
            for field in fields.reverse do
              equation ← mkAppM ``Exists #[← mkLambdaFVars #[field] equation]
            return equation
          mkForallFVars #[input] (← mkArrow accepted result)
        if proposition.hasFVar then continue
        let proof ← withLCtx {} {} <| mkFreshExprSyntheticOpaqueMVar proposition
        trace[lynx] "proving summary: {proposition}"
        setGoals [proof.mvarId!]
        let (_, next) ← proof.mvarId!.intros
        setGoals [next]
        search (← mkSolver) 24
        unless (← getGoals).isEmpty do
          saved.restore
          continue
        let proof ← instantiateMVars proof
        let next ← goal.assert (← mkFreshUserName `normal_return) proposition proof
        let (_, next) ← next.intro1
        setGoals [next]
        break
      catch e =>
        trace[lynx] "summary failed: {e.toMessageData}"
        saved.restore

private def solveGoal (fuel : Nat) : TacticM Unit := do
  if ← solveCoverage then return
  let solver ← mkSolver
  let start ← IO.monoMsNow
  unless (← getMainTarget).isAppOf ``Exists do synthesizeSummaries solver
  trace[lynx] "summary time: {(← IO.monoMsNow) - start}ms"
  search solver fuel
  trace[lynx] "solver time: {(← IO.monoMsNow) - start}ms"

private def isCoverageGoal (goal : MVarId) : MetaM Bool := goal.withContext do
  let target ← goal.getType
  return target.isAppOf ``Covered || (← hasCoverageTag goal)

/-- Generate coverage and behavioral verification conditions. -/
private partial def generate : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
    let target ← withTransparency .reducible <| whnf (← instantiateMVars (← goal.getType))
    if target.isAppOf ``WithSourceLabel then
      let args := target.getAppArgs
      let fileExpr ← whnf (← mkAppM ``SourceLabel.file #[args[0]!])
      let lineExpr ← whnf (← mkAppM ``SourceLabel.line #[args[0]!])
      if let (some file, some line) := (getStringValue? fileExpr, ← getNatValue? lineExpr) then
        goal.setTag (Name.mkSimple (toString ({ file, line } : SourceLabel)))
      let goal ← goal.change args[1]!
      replaceMainGoal [goal]
      generate
    else if target.isAppOf ``EnsuresClauses then
      replaceMainGoal [← goal.change (← whnf target)]
      generate
    else if target.isAppOf ``Covered then
      goal.setTag `coverage
      replaceMainGoal [goal]
    else if target.isAppOf ``Satisfies || target.isAppOf ``Property then
      let isContract := target.isAppOf ``Satisfies
      let source ← goal.getTag
      if source.isAnonymous then goal.setTag (if isContract then `ensures else `property)
      let goal ← goal.change (← whnf target)
      let obligations ← goal.apply (← mkConstWithFreshMVarLevels ``And.intro)
      let coverage := obligations[0]!
      let behavior := obligations[1]!
      coverage.setTag (if source.isAnonymous then `coverage else source ++ `coverage)
      behavior.setTag (if source.isAnonymous then
        (if isContract then `ensures else `property) else source)
      setGoals [behavior]
      let (introduced, behavior) ← behavior.intros
      replaceMainGoal [behavior]
      if let some arg := introduced[0]? then
        behavior.withContext do
          let type ← inferType (mkFVar arg)
          if isStructure (← getEnv) (type.getAppFn.constName?.getD .anonymous) then
            let branches ← behavior.cases arg
            replaceBranches (branches.toList.map (·.mvarId))
      setGoals (coverage :: (← getGoals))
    else
      let reduced ← whnf target
      if reduced.isAppOf ``And then
        replaceMainGoal (← goal.apply (← mkConstWithFreshMVarLevels ``And.intro))
        allGoals generate
      else if reduced.isConstOf ``True then
        goal.assign (mkConst ``True.intro)
        replaceMainGoal []
      else if reduced != target then
        replaceMainGoal [← goal.change reduced]
        generate
      else
        let (_, goal) ← goal.intros
        replaceMainGoal [goal]

elab "lynx_vcgen" : tactic => focus generate
elab "lynx_solve" : tactic => focus (solveGoal 24)
elab "lynx_verify" : tactic => focus do
  generate
  allGoals (solveGoal 24)
  let mut coverageFailed := false
  for goal in ← getGoals do
    if ← isCoverageGoal goal then coverageFailed := true
  if coverageFailed then
    throwError "lynx: could not prove that `expects` accepts any input; it may be empty or unsupported by automatic coverage"

end Lynx.Tactic
