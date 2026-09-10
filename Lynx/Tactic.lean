import Lean
import Lynx.Term
import Lynx.Attribute
import Lynx.Tactic.Contract
import Lynx.Term.Induction

/-!
# How the Lynx tactic works

`lynx_verify` proves translated Elixir contracts using the executable Lean
definitions themselves. It does not require a semantic theorem for every
function, nor an annotation on every translated definition.

## Contract generation

`Satisfies function expects ensures` is deliberately a conjunction:

```lean
Covered expects ∧
  ∀ input env, Accepted (expects input) env →
    ∃ result final, function input env = .ok result final ∧
      Accepted (ensures input result) final
```

`Property expects expression` has the same `Covered expects` conjunct. Thus a
proof can never succeed merely because the expectation accepts no input/state
pairs. `Accepted computation env` requires a normal return of exactly
`Term.true`, with any final state; false, non-boolean values, and exceptions are
not accepted. Expectations observe the initial environment and guarantees
observe the returned environment. Their own state changes are discarded, so
checking a contract cannot change the implementation's execution state.

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
and local hypotheses. It follows definitions whose result is `Result`, then
builds one local simplification context from those executable bodies. This is
why ordinary translated functions need no registration attribute or separate
semantics file. Library-level, kernel-proved `@[simp]` rules supplement the
executable bodies, including generic `Result` reductions; translated functions
themselves can remain annotation-free. Mark a library abstraction `@[lynx_opaque]`
to stop discovery at that function and use its specifications instead. This
also stops domain/return-summary discovery through its body. It is a proof-search
boundary, not Lean's `opaque`: kernel conversion, explicit unfolding and concrete
coverage evaluation remain available. The library uses the `_spec` suffix for these
theorems. Their statements and `@[simp]` attributes drive rewriting; that naming
convention is not a discovery rule.

Search substitutes equalities introduced by specifications before normalization.
When simplifying the target, whole local assumptions can discharge specification
premises, including quantified invariants; their bodies need not become global
rewrite rules. No operation names or representation types are hardcoded for this.

Normalization makes one ordered pass over non-quantified hypotheses, starting
with expectation-derived constraints. If that exposes structural facts, target
simplification is deferred until search unpacks them and substitutes the newly
known inputs. Otherwise the target is simplified immediately. Each
updated fact immediately replaces its old rewrite rule, so duplicate facts
cannot both disappear by simplifying each other to `True`. This normalization
pass does not add quantified hypotheses as local simp rules; separate guarded
application handles induction hypotheses and summaries. Known success/error
equations are also registered as pre-order rules, so executable unfolding
cannot hide their left-hand sides. A temporarily erased rule is explicitly
re-enabled when its hypothesis is retained, even if simplification did not
change that hypothesis. An unchanged hypothesis also reuses its existing rule
instead of rebuilding its simp-theorem entries.
Rejected input branches usually close before the implementation's possible
results are explored.

## Propagating acceptance requirements

An expectation is accepted only when its final outcome is
`.ok (Term.atom "true") final`. The solver uses Lean's built-in case splitting and
simplification to propagate the required result backward through executable
matches. For example:

```lean
(match input with
 | .nil => Result.ok (Term.atom "true")
 | _ => .ok (Term.atom "false")) = .ok (Term.atom "true")
```

forces `input = Term.nil`: simplification closes the rejected branch. Multiple
accepting branches remain separate proof obligations, retaining constructor
fields, wildcard exclusions, and named discriminant equations. Search splits
match-bearing hypotheses and simplifies the resulting constraints, eliminating
impossible outcomes before exploring more implementation results. Immediately
after constructor cases, it simplifies the affected hypothesis so rejected
branches need not enter another full normalization/search round.

The order matters for recursive proofs. Early splitting protects a recorded
input when the discriminant is that variable itself, preserving it for
induction. A compound computation depending on the input may still be split:
Lean's splitter retains the connection to that computation while leaving the
input available for induction. Later search can split the input if induction
is not applicable.

`lynx_vcgen` emits conditions about the original executable expressions.
Coverage and call-premise proofs use the same built-in splitting/simplification
machinery. Implementation binds remain shared until their outcomes are needed.

Only the final accepted outcome is restricted to `true`. Intermediate false,
non-boolean, and exceptional outcomes retain their executable meaning.
Coverage still requires an actual input satisfying the executable expectation.

## Bounded search

`solveGoal` first attempts coverage, then builds a solver context if needed.
When recursive definitions are present, it attempts summary synthesis before
the main search, including for return contracts. Each main search call follows
this order; structural changes and
successful hypothesis applications recurse with less fuel on the resulting
goals:

1. Introduce binders and solve a `Covered` goal by testing a small set of
   concrete `Term`, tuple, unit, or structure values, with empty initial
   environments. First try definitional equality on
   every candidate, inferring the actual final environment without elaborating
   a tactic or building a simp context; concrete term and tuple candidates are
   built directly as expressions in the same bounded order. If
   none succeeds, fall back to the guard prover. A candidate is accepted only
   after proving the real executable expectation; the candidate list is not
   treated as a model of the domain.
2. Destructure already exposed conjunctions, disjunctions, existentials, and
   products before normalizing again. Otherwise normalize hypotheses and the
   target when no new structural facts were exposed, then try destructuring.
   This avoids a full normalization pass per
   constructor, while letting normalization eliminate trivial state witnesses
   before unfolding an `Accepted` hypothesis into an existential.
3. Split eligible hypothesis matches before exploring returned values,
   protecting recorded input variables so they remain available for induction.
4. Specialize a synthesized summary when applicable, or apply a hypothesis with
   a propositional premise. State-generalized hypotheses are specialized at
   environments of relevant calls; repeated specializations are tracked and,
   when fully determined, skipped before reproving their premises.
   Each application must first prove its premise in a
   separate goal. Premise preparation attempts to clear quantified hypotheses
   and unrelated assumptions, retaining any required by local dependencies.
5. Try assumptions, reflexivity, `omega`, and `grind` with case splitting
   disabled.
6. Induct on a recorded `Term` input used as the structural argument of a
   discovered recursive definition. Simplify branch targets and try to remove
   induction hypotheses irrelevant to remaining recursive calls. More than one
   independent input may be inducted. Environments are generalized before
   induction so hypotheses remain usable after state-changing calls.
7. Generalize and split one shared monadic computation, retaining an equation
   for its outcome. This avoids duplicating nested bind continuations before
   its `EStateM.Result.ok`/`EStateM.Result.error` outcome and returned state are known.
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

1. Find discovered recursive functions of type `Term → Result`.
2. Find candidate input domains inside existing `Accepted` hypotheses, looking
   through executable wrappers with bounded traversal.
3. Look for a single candidate `Term` constructor in normal returns from the
   function body and the executable callees it follows.
4. Construct a normal-return proposition and prove it in a fresh context using
   the same bounded search, or reuse an identical closed proof from the local
   environment cache.
5. Add the summary only if that independent proof closed completely.

The summary is a proved local theorem, never an assumption or a reuse of
another application contract. Current summaries assert equality to a
state-preserving `Result.ok` computation, with a domain accepted from empty
state. This stronger, state-independent claim is useful for existing pure
functions and must itself be proved; it is not assumed for stateful functions.
For an initially existential target, such as a return contract, the solver may
use a summary immediately. For relational properties it waits until after
induction, preserving the executable calls needed to discover that induction.
It still proves the corresponding domain constraint before
using the summary; it does not invent a domain for arbitrary intermediate
results. Current synthesis handles unary functions with a uniform candidate
result constructor when bounded search can prove the conjecture. It is not
general invariant discovery.

Summary caching is keyed by the entire closed proposition, including its
domain and result constructor. Neither local assumptions nor unresolved
metavariables can enter the cache. The cache follows environment snapshots,
so speculative branches roll it back; it is not serialized into imports or
shared across fresh Lean processes. Sequential proofs in one module can reuse
it, while asynchronous elaboration keeps caches local. Every resulting theorem
still undergoes kernel checking; a cached return shape does not discharge a
call's domain or establish a stronger guarantee.

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

/-- Closed proofs only; environment snapshots handle rollback and asynchronous
elaboration. This cache is not serialized into imported modules. -/
private initialize summaryProofs : EnvExtension (ExprMap Expr) ←
  registerEnvExtension (pure {}) (asyncMode := .local)

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
  applications : ExprSet := {}
  summarizeRoot : Bool := false

/-- Recognize Erlang results, whose success type is `Term`. -/
private def isResultType (type : Expr) : MetaM Bool := do
  if type.isAppOfArity ``Result 1 && type.getAppArgs[0]!.isConstOf ``Term then return true
  let type ← whnf type
  return type.isAppOfArity ``EStateM.Result 3 &&
    type.getAppArgs[0]!.isConstOf ``Exception &&
    type.getAppArgs[1]!.isConstOf ``Environment &&
    type.getAppArgs[2]!.isConstOf ``Term

/-- Discover executable definitions by their result type, following their calls.
Their bodies supply reduction rules alongside registered library simp theorems;
translated definitions need no separate semantic theorem. -/
private def mkSolver (unfoldOpaque? : Option Name := none) : TacticM Solver := withMainContext do
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
    if opaqueAttr.hasTag (← getEnv) name && unfoldOpaque? != some name then continue
    let .defnInfo info ← getConstInfo name | continue
    let executable ← forallTelescopeReducing info.type fun _ result =>
      isResultType result
    unless executable do continue
    definitions := definitions.push (mkIdent name)
    if ← isRecursiveDefinition name then
      recursive := recursive.push name
      if let some index ← getStructuralRecArgPos? name then
        majors := majors.insert name index
    pending := pending ++ info.value.getUsedConstants
  -- Preserve executable bind structure for branch discovery; the generic
  -- lawful-monad rewrites reassociate binds or turn them into functor maps.
  let simpSyntax ← `(tactic| simp_all (config := { failIfUnchanged := false })
    [Accepted, Term.true, Term.false, and_assoc,
    Pure.pure, EStateM.pure, -bind_assoc, -bind_pure_comp, $[$definitions:ident],*])
  let result ← mkSimpContext simpSyntax (eraseLocal := true) (kind := .simpAll)
  return ⟨result.ctx, result.simprocs, recursive, majors, inputs, false, {},
    (← getMainTarget).isAppOf ``Exists⟩

/-- Keep quantified invariants available as whole premises of specification
lemmas, without installing their bodies as unrestricted rewrite rules. -/
private def dischargeAssumption : Simp.Discharge := fun proposition => do
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      if decl.type == proposition then return some decl.toExpr
      -- A simp premise is a proposition: data variables cannot prove it.
      -- Keep proposition wrappers too, including abstract library invariants.
      unless ← isProp decl.type do continue
      if ← isDefEq decl.type proposition then return some decl.toExpr
  -- Preserve standard recursive simp discharge for composed conditional specs.
  Simp.dischargeDefault? proposition

/-- Rewrite known computation outcomes before their executable head unfolds.
Post-order rewriting alone can lose the matching call during descent. -/
private def addFact (context : Simp.Context) (h : FVarId) : MetaM Simp.Context := do
  let mut thms ← context.simpTheorems.addTheorem
    (.fvar h) (mkFVar h) (config := context.indexConfig)
  let type ← h.getType
  if type.isAppOf ``Eq then
    let rhs := type.getAppArgs[2]!
    if rhs.isAppOf ``Result.ok || rhs.isAppOf ``Result.error ||
        rhs.isAppOf ``EStateM.Result.ok || rhs.isAppOf ``EStateM.Result.error then
      thms ← thms.modifyM 0 fun set => set.add (.fvar h) #[] (mkFVar h)
        (post := false) (config := context.indexConfig)
  -- Removing a rule while simplifying its own hypothesis marks its origin as
  -- erased. Re-adding an unchanged hypothesis does not clear that marker.
  return context.setSimpTheorems (thms.map (·.unerase (.fvar h)))

/-- One forward pass; search revisits normalization after structural progress.
Do not repeatedly traverse quantified recursive proofs as `simpAll` does. -/
private def normalize (solver : Solver) : TacticM Bool := do
  let start ← IO.monoMsNow
  let mut goal ← getMainGoal
  let (hypotheses, context) ← goal.withContext do
    let hypotheses ← (← getPropHyps).filterM fun h => return !(← h.getType).isForall
    let mut context := solver.context
    for h in hypotheses do
      context ← addFact context h
    let constraints ← hypotheses.filterM fun h => do
      let decl ← h.getDecl
      return !decl.userName.toString.startsWith "recursive_result" &&
        (decl.type.isAppOf ``Accepted ||
          (decl.type.isAppOf ``Eq &&
            (decl.type.getAppArgs[2]!.isAppOf ``Result.ok ||
              decl.type.getAppArgs[2]!.isAppOf ``EStateM.Result.ok)))
    return (constraints ++ hypotheses.filter (fun h => !constraints.contains h), context)
  let mut context := context
  for h in hypotheses do
    -- Replace rules immediately: simplifying all facts against the original
    -- set could turn both copies of a duplicate hypothesis into `True`.
    context := context.setSimpTheorems (context.simpTheorems.eraseTheorem (.fvar h))
    let oldType ← goal.withContext h.getType
    let oldId := h
    let (result, _) ← simpLocalDecl goal h context solver.simprocs
    let some (h, next) := result | setGoals []; return true
    goal := next
    let type ← goal.withContext h.getType
    if type.isTrue then
      goal ← goal.tryClear h
    else if h == oldId && type == oldType then
      context := context.setSimpTheorems
        (context.simpTheorems.map (·.unerase (.fvar h)))
    else
      context ← goal.withContext do
        addFact context h
  -- Expose newly learned inputs before exploring implementation outcomes.
  -- Search will unpack these facts and substitute their equalities first.
  let exposed ← goal.withContext do
    return (← getLCtx).any fun decl =>
      let type := decl.type.consumeMData
      !decl.isImplementationDetail &&
        (type.isAppOf ``Exists || type.isAppOf ``And || type.isAppOf ``Or || type.isAppOf ``Prod)
  if exposed then
    trace[lynx] "normalize (deferred target): {(← IO.monoMsNow) - start}ms"
    replaceMainGoal [goal]
    return false
  let (result, _) ← simpTarget goal context solver.simprocs (some dischargeAssumption)
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

private def destructFacts (reduce : Bool := true) : TacticM Bool := withMainContext do
  let goal ← getMainGoal
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      let type ← if reduce then whnf decl.type else pure decl.type.consumeMData
      if type.isAppOf ``Exists || type.isAppOf ``And || type.isAppOf ``Or || type.isAppOf ``Prod then
        let branches ← goal.cases decl.fvarId
        replaceBranches (branches.toList.map (·.mvarId))
        return true
  return false

/-- Built-in splitting and simplification, including compound computations.
Early calls protect bare induction inputs, not computations containing them;
later calls prioritize recursive results. -/
private def splitHypothesis (solver : Solver) (protectedInputs : Array FVarId := #[])
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
        if e.hasLooseBVars then return
        if let some matcher ← matchMatcherApp? e then
          for discr in matcher.discrs do
            if discr.isFVar && !protectedInputs.contains discr.fvarId! then
              discriminants.modify (·.push discr.fvarId!)
      for discr in ← discriminants.get do
        let branches ← goal.cases discr
        let mut remaining := []
        for branch in branches do
          -- Reject impossible constructor branches using only the affected fact.
          -- Full normalization would also revisit every other fact and the target.
          let hypothesis := branch.subst.apply decl.toExpr
          if hypothesis.isFVar then
            let (result, _) ← simpLocalDecl branch.mvarId hypothesis.fvarId!
              solver.context solver.simprocs
            if let some (_, next) := result then remaining := remaining ++ [next]
          else
            remaining := remaining ++ [branch.mvarId]
        replaceBranches remaining
        return true
      if let some candidate ← findSplit? decl.type then
        if let some matcher ← matchMatcherApp? candidate then
          -- A compound discriminant can be generalized without choosing the
          -- constructor of the recursive input it depends on.
          if matcher.discrs.any (fun d => d.isFVar && protectedInputs.contains d.fvarId!) then
            continue
      let saved ← saveState
      try
        if let some branches ← splitLocalDecl? goal decl.fvarId then
          replaceBranches branches
          return true
      catch _ => saved.restore
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
      -- A preceding recursive call may change state before the next call.
      -- Generalize environments so induction hypotheses apply to that state too.
      let environments := (← getLCtx).foldl (init := #[]) fun envs decl =>
        if decl.type.isConstOf ``Environment then envs.push decl.fvarId else envs
      let (_, generalized) ← goal.revert environments
      let branches ← generalized.induction input ``Lynx.Term.induct
      let mut remaining := []
      for branch in branches do
        let (_, introduced) ← branch.mvarId.intros
        let (simplified, _) ← simpTarget introduced solver.context solver.simprocs
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
      unless e.isApp && !e.hasLooseBVars do return
      if !(← matchMatcherApp? e).isSome &&
          (← inferType e).isAppOf ``EStateM.Result &&
          !e.isAppOf ``EStateM.Result.ok && !e.isAppOf ``EStateM.Result.error then
        candidates.modify (·.push e)
      if e.isAppOf ``Bind.bind then
        let args := e.getAppArgs
        if args.size >= 2 then
          let computation := args[args.size - 2]!
          unless computation.hasLooseBVars do
            if !computation.isAppOf ``Bind.bind && !computation.isAppOf ``Result.ok &&
                !computation.isAppOf ``Result.error && (← isResultType (← inferType computation)) then
              candidates.modify (·.push computation)
    for computation in ← candidates.get do
      if (← getLCtx).any (fun decl => decl.type.isAppOf ``Eq &&
          decl.type.getAppArgs[1]! == computation &&
          (decl.type.getAppArgs[2]!.isAppOf ``EStateM.Result.ok ||
            decl.type.getAppArgs[2]!.isAppOf ``EStateM.Result.error)) then continue
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
  else if ← splitHypothesis solver then
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
  if type.isConstOf ``Environment then
    return #[← elabTerm (← `(({} : Environment))) (some type)]
  if type.isConstOf ``Term then
    let zero := mkApp (mkConst ``Term.integer) (mkIntLit 0)
    let nil := mkConst ``Term.nil
    let atom := mkApp (mkConst ``Term.atom) ∘ mkStrLit
    return #[
      zero, nil, mkConst ``Term.emptyMap, atom "", atom "true",
      mkApp2 (mkConst ``Term.cons) zero nil,
      mkApp2 (mkConst ``Term.cons) (atom "") nil]
  if type.isAppOf ``Prod then
    let args := type.getAppArgs
    let left ← coverageCandidates args[0]! (depth - 1)
    let right ← coverageCandidates args[1]! (depth - 1)
    let constructor := mkApp2 (mkConst ``Prod.mk type.getAppFn.constLevels!) args[0]! args[1]!
    let mut result := #[]
    for l in left do
      for r in right do result := result.push (mkApp2 constructor l r)
    return result
  if ← isDefEq type (mkConst ``Unit) then return #[mkConst ``Unit.unit]
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
  let rawTarget := (← instantiateMVars (← goal.getType)).consumeMData
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
          -- Infer the observed final state by conversion, without elaborating
          -- a failing `exact` tactic (and its diagnostic) for every candidate.
          let accepted ← whnf proposition
          unless accepted.isAppOf ``Exists do saved.restore; continue
          let acceptedArgs := accepted.getAppArgs
          let final ← mkFreshExprMVar acceptedArgs[0]!
          let equation ← whnf (mkApp acceptedArgs[1]! final)
          unless equation.isAppOf ``Eq do saved.restore; continue
          let equationArgs := equation.getAppArgs
          unless ← isDefEq equationArgs[1]! equationArgs[2]! do saved.restore; continue
          let final ← instantiateMVars final
          if final.hasExprMVar then saved.restore; continue
          let .sort level ← whnf (← inferType acceptedArgs[0]!) | saved.restore; continue
          proof.mvarId!.assign (mkAppN (mkConst ``Exists.intro [level])
            #[acceptedArgs[0]!, acceptedArgs[1]!, final, ← mkEqRefl equationArgs[1]!])
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

private def applyHypothesis (solver : Solver) : TacticM (Option Solver) := withMainContext do
  let goal ← getMainGoal
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      let type ← whnf decl.type
      let .forallE _ domain _ _ := type | continue
      let mut candidates := #[decl.toExpr]
      if domain.isConstOf ``Environment then
        candidates := #[]
        for state in ← getLCtx do
          if state.type.isConstOf ``Environment then
            candidates := candidates.push (mkApp decl.toExpr state.toExpr)
        -- State changes often leave a structure expression, not a named local.
        -- Include environments actually passed to computations in the goal or
        -- observed outcomes, so recursive calls can use those states too.
        let mut expressions := #[← goal.getType]
        for fact in ← getLCtx do
          if !fact.type.isForall then expressions := expressions.push fact.type
        let states ← IO.mkRef ({} : ExprSet)
        for expression in expressions do
          expression.forEach fun e => do
            let .app _ env := e | return
            unless !e.hasLooseBVars do return
            if e.isAppOf ``EStateM.Result.ok || e.isAppOf ``EStateM.Result.error then return
            unless (← inferType e).isAppOf ``EStateM.Result do return
            if (← inferType env).isConstOf ``Environment then states.modify (·.insert env)
        for state in (← states.get).toArray do
          let candidate := mkApp decl.toExpr state
          unless candidates.contains candidate do candidates := candidates.push candidate
      else unless ← isProp domain do continue
      for candidate in candidates do
        let saved ← saveState
        try
          let mut specialized := candidate
          let mut type ← whnf (← inferType specialized)
          -- Remaining state witnesses are inferred while proving the premise.
          while type.isForall && type.bindingDomain!.isConstOf ``Environment do
            specialized := mkApp specialized (← mkFreshExprMVar (mkConst ``Environment))
            type ← whnf (← inferType specialized)
          -- Already-used specializations need no second premise proof. Keep
          -- the later check too: unresolved state witnesses may be inferred
          -- only while discharging the premise.
          if !specialized.hasExprMVar && solver.applications.contains specialized then
            saved.restore
            continue
          let mut value := specialized
          if let .forallE _ premise _ _ := type then
            unless ← isProp premise do saved.restore; continue
            let proof ← guardGoal premise
            proveGuard solver 8
            unless (← getGoals).isEmpty do saved.restore; continue
            value := mkApp specialized (← instantiateMVars proof)
          specialized ← instantiateMVars specialized
          if specialized.hasExprMVar || solver.applications.contains specialized then
            saved.restore
            continue
          let resultType ← inferType value
          if domain.isConstOf ``Environment then
            let target ← goal.getType
            let hasOutcome ← IO.mkRef false
            let outcomeRelevant ← IO.mkRef false
            let computationRelevant ← IO.mkRef false
            resultType.forEach fun e => do
              unless e.isApp && !e.hasLooseBVars do return
              if e.isAppOf ``EStateM.Result.ok || e.isAppOf ``EStateM.Result.error then return
              let type ← inferType e
              if type.isAppOf ``EStateM.Result then
                hasOutcome.set true
                if (target.find? (· == e)).isSome then outcomeRelevant.set true
              else if ← isResultType type then
                if (target.find? (· == e)).isSome then computationRelevant.set true
            let mut relevant ← if ← hasOutcome.get then outcomeRelevant.get else computationRelevant.get
            if !relevant then
              -- Calls below a bind have a bound environment in the theorem.
              -- Match their computation against actual calls at the chosen
              -- state, including calls already evaluated into local equations.
              let state := candidate.getAppArgs.back!
              let found ← IO.mkRef false
              let mut expressions := #[target]
              for fact in ← getLCtx do
                if !fact.type.isForall then expressions := expressions.push fact.type
              for expression in expressions do
                expression.forEach fun e => do
                  let .app computation env := e | return
                  unless !e.hasLooseBVars && env == state do return
                  if e.isAppOf ``EStateM.Result.ok || e.isAppOf ``EStateM.Result.error then return
                  unless (← inferType e).isAppOf ``EStateM.Result do return
                  if (resultType.find? (· == computation)).isSome then found.set true
              relevant ← found.get
            unless relevant do saved.restore; continue
          let next ← goal.assert (← mkFreshUserName `recursive_result) resultType value
          let (_, next) ← next.intro1
          setGoals [next]
          return some { solver with applications := solver.applications.insert specialized }
        catch _ => saved.restore
  return none

private def applySummary (solver : Solver) : TacticM Bool := withMainContext do
  unless solver.inducted || solver.summarizeRoot do return false
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
        -- Prove the real expectation, allowing stateful observations to have
        -- normalized into equations about pure callbacks. Syntactic occurrence
        -- of the original wrapper is no longer a reliable applicability test.
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
  replaceMainGoal [← substVars goal]
  if ← solveCoverage (some solver) then return
  if ← destructFacts false then
    allGoals (search solver (fuel - 1))
    return
  if ← normalize solver then return
  if ← destructFacts then
    allGoals (search solver (fuel - 1))
    return
  if ← splitHypothesis solver solver.inputs true then
    allGoals (search solver (fuel - 1))
    return
  if ← applySummary solver then
    search solver (fuel - 1)
    return
  if let some solver ← applyHypothesis solver then
    search solver (fuel - 1)
    return
  if ← closeLeaf then return
  if let some solver ← inductInput solver then
    allGoals (search solver (fuel - 1))
    return
  if ← splitComputation then
    allGoals (search solver (fuel - 1))
    return
  if ← splitHypothesis solver then
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
      if ← isResultType (← inferType expression) then result := result.push fn
    if let .const name _ := expression.getAppFn then
      if !opaqueAttr.hasTag (← getEnv) name && !(← isRecursiveDefinition name) then
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
    if opaqueAttr.hasTag (← getEnv) name then continue
    let .defnInfo info ← getConstInfo name | continue
    info.value.forEach fun e => do
      if e.isAppOfArity ``Result.ok 2 then
        let returned := e.getAppArgs[1]!
        if let .const ctor _ := returned.getAppFn then
          if let .ctorInfo ci ← getConstInfo ctor then
            if ci.induct == ``Term then constructors.modify (·.insert ctor)
    for callee in info.value.getUsedConstants do
      if callee == function then continue
      let .defnInfo calleeInfo ← getConstInfo callee | continue
      if ← forallTelescopeReducing calleeInfo.type fun _ result => isResultType result then
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
    unless ← isDefEq info.type (← elabTerm (← `(Term → Result)) none) do continue
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
          let accepted ← mkAppM ``Accepted #[mkApp domain input,
            ← elabTerm (← `(({} : Environment))) none]
          let result ← forallTelescope (← inferType (mkConst constructor)) fun fields _ => do
            let value ← mkAppM ``Result.ok #[mkAppN (mkConst constructor) fields]
            let mut equation ← mkEq (mkApp (mkConst function) input) value
            for field in fields.reverse do
              equation ← mkAppM ``Exists #[← mkLambdaFVars #[field] equation]
            return equation
          mkForallFVars #[input] (← mkArrow accepted result)
        let proposition ← instantiateMVars proposition
        if proposition.hasFVar || proposition.hasMVar then continue
        let proof ← if let some proof := (summaryProofs.getState (← getEnv))[proposition]? then
          trace[lynx] "reusing summary: {proposition}"
          pure proof
        else
          let proof ← withLCtx {} {} <| mkFreshExprSyntheticOpaqueMVar proposition
          trace[lynx] "proving summary: {proposition}"
          setGoals [proof.mvarId!]
          let (_, next) ← proof.mvarId!.intros
          setGoals [next]
          search (← mkSolver) 24
          unless (← getGoals).isEmpty do
            throwError "summary proof did not close"
          let proof ← instantiateMVars proof
          if proof.hasMVar || proof.hasFVar then
            throwError "summary proof is not closed"
          modifyEnv fun env => summaryProofs.modifyState env (·.insert proposition proof)
          pure proof
        let next ← goal.assert (← mkFreshUserName `normal_return) proposition proof
        let (_, next) ← next.intro1
        setGoals [next]
        break
      catch e =>
        trace[lynx] "summary failed: {e.toMessageData}"
        saved.restore

private def solveGoal (fuel : Nat) : TacticM Unit := do
  let coverageStart ← IO.monoMsNow
  if ← solveCoverage then
    trace[lynx] "coverage time: {(← IO.monoMsNow) - coverageStart}ms"
    return
  let setupStart ← IO.monoMsNow
  let solver ← mkSolver
  trace[lynx] "setup time: {(← IO.monoMsNow) - setupStart}ms"
  let start ← IO.monoMsNow
  unless solver.recursive.isEmpty do synthesizeSummaries solver
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
elab "lynx_pure_solve " function:ident : tactic => focus <| withMainContext do
  let function ← resolveGlobalConstNoOverload function
  let solver ← mkSolver (some function)
  let goal ← getMainGoal
  let target ← goal.getType
  for input in solver.inputs do
    if (target.find? fun expression =>
        match solver.majors.find? (expression.getAppFn.constName?.getD .anonymous) with
        | some index => expression.getAppArgs[index]? == some (mkFVar input)
        | none => false).isSome then
      let generalized := (← getLCtx).foldl (init := #[]) fun variables decl =>
        if decl.type.isConstOf ``Term && decl.fvarId != input then variables.push decl.fvarId
        else variables
      let (_, goal) ← goal.revert generalized
      let branches ← goal.induction input ``Lynx.Term.induct
      replaceBranches (branches.toList.map (·.mvarId))
      let definitions := solver.recursive.map mkIdent
      let finish ← `(tacticSeq| intros; simp_all [$[$definitions:ident],*])
      allGoals (evalTactic finish)
      return
  if solver.recursive.isEmpty then
    for input in solver.inputs do
      allGoals <| withMainContext do
        let goal ← getMainGoal
        if (← getLCtx).contains input then
          let branches ← goal.cases input
          replaceBranches (branches.toList.map (·.mvarId))
    let functionId := mkIdent function
    let finish ← `(tacticSeq|
      simp_all [$functionId:ident]
      repeat' first | split at * | simp_all)
    allGoals (evalTactic finish)
    return
  search solver 24
elab "lynx_verify" : tactic => focus do
  generate
  allGoals (solveGoal 24)
  let mut coverageFailed := false
  for goal in ← getGoals do
    if ← isCoverageGoal goal then coverageFailed := true
  if coverageFailed then
    throwError "lynx: could not prove that `expects` accepts any input; it may be empty or unsupported by automatic coverage"

/-- Elaborate a definition and prove once that each fully applied computation
neither reads nor changes the environment. The generated `<name>_pure` theorem
is a simp rule, so execution facts for callers reduce back to ordinary
computation equalities. -/
elab doc?:(docComment)? "#lynx_pure " declaration:command : command => do
  if let some doc := doc? then
    unless declaration.raw.getArg 0 |>.getArg 0 |>.isNone do
      throwErrorAt doc "#lynx_pure declaration has two documentation comments"
  let declaration : TSyntax `command := match doc? with
    | some doc =>
        let modifiers := declaration.raw.getArg 0
        let modifiers := modifiers.setArg 0 (mkNullNode #[doc.raw])
        ⟨declaration.raw.setArg 0 modifiers⟩
    | none => declaration
  let inner := declaration.raw.getArg 1
  unless inner.getKind == ``Lean.Parser.Command.definition do
    throwErrorAt declaration "#lynx_pure must wrap a `def` declaration"
  let declId := inner.getArg 1
  let id := if declId.isIdent then declId else declId.getArg 0
  unless id.isIdent do
    throwErrorAt declId "could not determine the definition name"
  Command.elabCommand declaration
  let function ← resolveGlobalConstNoOverload id
  let info ← getConstInfo function
  let levels := info.levelParams.map Level.param
  let functionExpr := mkConst function levels
  let purityType ← Command.liftTermElabM do
    forallTelescopeReducing info.type fun arguments resultType => do
      unless resultType.isAppOf ``EStateM.Result && !arguments.isEmpty &&
          (← inferType arguments.back!).isConstOf ``Environment do
        throwErrorAt declId "#lynx_pure requires a definition returning `Result`"
      let inputs := arguments.pop
      let proposition ← mkAppM ``Result.IsPure #[mkAppN functionExpr inputs]
      mkForallFVars inputs proposition
  let proof ← Command.liftTermElabM do
    let functionId := mkIdent function
    let proofSyntax ← if ← isRecursiveDefinition function then
      `(by intros; lynx_pure_solve $functionId:ident)
    else
      `(by
        intros
        first
        | (simp only [$functionId:ident]
           repeat' first | split | simp_all
           all_goals repeat' first | split at * | simp_all
           all_goals lynx_solve
           done)
        | lynx_pure_solve $functionId:ident)
    let proof ← Term.elabTermEnsuringType
      proofSyntax
      purityType
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars proof
  let theoremName := function.getPrefix ++
    Name.mkSimple (function.getString! ++ "_pure")
  Command.liftCoreM <| addAndCompile <| Declaration.thmDecl {
    name := theoremName
    levelParams := info.levelParams
    type := purityType
    value := proof
  }
  Command.elabCommand (← `(attribute [simp↓] $(mkIdent theoremName)))

end Lynx.Tactic
