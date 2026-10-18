module

public meta import Lean
public import Lynx.Term

public section

-- Retain successful-return equations while checking well-founded recursion.
-- Only computations with a kernel-checked purity proof use these rewrites.
@[expose] public def Lynx.Result.bindPure (computation : Lynx.Result α)
    (pure : computation.IsPure)
    (next : {value : α // computation = .ok value} → Lynx.Result β) : Lynx.Result β :=
  match (generalizing := false) returned : computation with
  | .ok value => next ⟨value, returned⟩
  | .error exception => .error exception
  | .exhausted | .apply .. | .get .. | .set .. | .spawn .. | .schedule .. |
      .send .. | .receive .. => False.elim (by simp_all [Lynx.Result.IsPure])

@[wf_preprocess] public theorem Lynx.Result.bindPure_eq
    (computation : Lynx.Result α) (pure : computation.IsPure) (next : α → Lynx.Result β) :
    (computation >>= next) = computation.bindPure pure
      (fun value => binderNameHint value next (next (wfParam value.val))) := by
  cases computation <;> first | rfl | exact False.elim pure

@[wf_preprocess] public theorem Lynx.Result.bindPure_explicit
    (computation : Lynx.Result α) (pure : computation.IsPure) (next : α → Lynx.Result β) :
    Lynx.Result.bind computation next = computation.bindPure pure
      (fun value => binderNameHint value next (next (wfParam value.val))) :=
  Lynx.Result.bindPure_eq computation pure next

/-- Erlang guards select their body only on the atom `true`. -/
@[expose] public def Lynx.Result.guardPassed : Lynx.Result → Bool
  | .ok (.atom value) => value == "true"
  | _ => false

/-- Run a Core guard, falling through on exceptions and values other than `true`. -/
@[expose] public def Lynx.Result.guard (computation : Lynx.Result)
    (body next : Unit → Lynx.Result α) : Lynx.Result α :=
  computation.tryWith
    (fun value => match value with | .atom "true" => body () | _ => next ())
    (fun _ => next ())

@[simp] public theorem Lynx.Result.guard_eq (computation : Lynx.Result)
    (body next : Unit → Lynx.Result α) :
    computation.guard body next = computation.tryWith
      (fun value => match value with | .atom "true" => body () | _ => next ())
      (fun _ => next ()) := rfl

@[simp↓] public theorem Lynx.Result.IsPure.guard (computation : Lynx.Result)
    (body next : Unit → Lynx.Result α) (pure : computation.IsPure)
    (bodyPure : ∀ token, (body token).IsPure) (nextPure : ∀ token, (next token).IsPure) :
    (computation.guard body next).IsPure := by
  unfold Lynx.Result.guard
  apply Lynx.Result.IsPure.tryWith _ _ _ pure
  · intro value
    split <;> simp_all
  · exact fun _ => nextPure ()

@[wf_preprocess] public theorem Lynx.Result.guard_wf
    (computation : Lynx.Result) (pure : computation.IsPure)
    (body next : Unit → Lynx.Result α) :
    computation.guard body next =
      (if computation.guardPassed then body () else next ()) := by
  cases computation with
  | ok value =>
    simp only [Lynx.Result.guard_eq, Lynx.Result.tryWith_ok]
    cases value <;> simp [Lynx.Result.guardPassed]
    rename_i value
    by_cases accepted : value = "true" <;> simp_all
  | error exception => rfl
  | _ => exact False.elim pure

/-- Recursive purity proofs can use the equation for a successful bind. -/
public theorem Lynx.Result.IsPure.bind_return (computation : Lynx.Result α)
    (next : α → Lynx.Result β) (pure : computation.IsPure)
    (nextPure : ∀ value, computation = .ok value → (next value).IsPure) :
    (computation >>= next).IsPure := by
  cases computation <;> simp_all [Lynx.Result.IsPure]

public theorem Lynx.Result.IsPure.bind_return_explicit (computation : Lynx.Result α)
    (next : α → Lynx.Result β) (pure : computation.IsPure)
    (nextPure : ∀ value, computation = .ok value → (next value).IsPure) :
    (Lynx.Result.bind computation next).IsPure :=
  Lynx.Result.IsPure.bind_return computation next pure nextPure

public theorem Lynx.Result.IsPure.guard_cases (computation : Lynx.Result)
    (body next : Unit → Lynx.Result α) (pure : computation.IsPure)
    (onTrue : computation.guardPassed = true → ∀ token, (body token).IsPure)
    (onFalse : computation.guardPassed = false → ∀ token, (next token).IsPure) :
    (computation.guard body next).IsPure := by
  rw [Lynx.Result.guard_wf computation pure]
  split <;> rename_i passed
  · exact onTrue passed ()
  · exact onFalse (by simpa using passed) ()

public theorem Lynx.Result.IsPartial.guard (computation : Lynx.Result)
    (body next : Unit → Lynx.Result α) (computationPartial : computation.IsPartial)
    (bodyPartial : ∀ token, (body token).IsPartial)
    (nextPartial : ∀ token, (next token).IsPartial) :
    (computation.guard body next).IsPartial := by
  unfold Lynx.Result.guard
  apply Lynx.Result.IsPartial.tryWith _ _ _ computationPartial
  · intro value
    split <;> simp_all
  · exact fun _ => nextPartial ()

/-- Recursive partiality proofs can use the equation for a successful bind. -/
public theorem Lynx.Result.IsPartial.bind_return (computation : Lynx.Result α)
    (next : α → Lynx.Result β) (computationPartial : computation.IsPartial)
    (nextPartial : ∀ value, computation = .ok value → (next value).IsPartial) :
    (computation >>= next).IsPartial := by
  change (Lynx.Result.bind computation next).IsPartial
  cases computation <;> simp_all [Lynx.Result.IsPartial, Lynx.Result.bind]

public theorem Lynx.Result.IsPartial.bind_return_explicit (computation : Lynx.Result α)
    (next : α → Lynx.Result β) (computationPartial : computation.IsPartial)
    (nextPartial : ∀ value, computation = .ok value → (next value).IsPartial) :
    (Lynx.Result.bind computation next).IsPartial :=
  Lynx.Result.IsPartial.bind_return computation next computationPartial nextPartial

public theorem Lynx.Result.IsPartial.guard_cases (computation : Lynx.Result)
    (body next : Unit → Lynx.Result α) (computationPartial : computation.IsPartial)
    (onTrue : computation.guardPassed = true → ∀ token, (body token).IsPartial)
    (onFalse : computation.guardPassed = false → ∀ token, (next token).IsPartial) :
    (computation.guard body next).IsPartial := by
  unfold Lynx.Result.guard
  cases computation with
  | ok value =>
    simp only [Lynx.Result.tryWith_ok]
    split
    · exact onTrue (by simp [Lynx.Result.guardPassed]) ()
    · rename_i other
      exact onFalse (by cases value <;> simp_all [Lynx.Result.guardPassed]) ()
  | error exception => exact onFalse rfl ()
  | exhausted => trivial
  | _ => exact False.elim computationPartial

public meta section

/-! Generate kernel-checked purity lemmas for translated functions.
Each definition gets an ordinary `<name>_pure` theorem, registered with `simp`.
Recursive definitions use their compiler-generated induction principle. -/
namespace Lynx.Purity
open Lean Meta Elab Tactic

/-- A predicate on computations proved structurally over translated code. -/
private structure Predicate where
  name : Name
  command : String
  property : String
  suffix : String
  terminals : List Name
  shared : Name
  rules : List (Name × Name)
  /-- Lemmas of a stronger predicate that imply this one, and the implication. -/
  stronger : Option (String × Name) := none

private def purePredicate : Predicate where
  name := ``Result.IsPure
  command := "#lynx_pure"
  property := "purity"
  suffix := "_pure"
  terminals := [``Result.ok, ``Result.error]
  shared := ``Result.IsPure.shared
  rules := [(``Bind.bind, ``Result.IsPure.bind), (``Result.bind, ``Result.IsPure.bind_explicit),
    (``Result.guard, ``Result.IsPure.guard), (``Result.tryWith, ``Result.IsPure.tryWith),
    (``Result.handle, ``Result.IsPure.handle), (``Result.orElse, ``Result.IsPure.orElse),
    (``Result.andAlso, ``Result.IsPure.andAlso),
    -- Bitstring extraction is defined later, with its rule.
    (`Lynx.Term.Bitstring.extract, `Lynx.Result.IsPure.extract)]

private def partialPredicate : Predicate where
  name := ``Result.IsPartial
  command := "#lynx_partial"
  property := "partiality"
  suffix := "_partial"
  terminals := [``Result.ok, ``Result.error, ``Result.exhausted]
  shared := ``Result.IsPartial.shared
  rules := [(``Bind.bind, ``Result.IsPartial.bind),
    (``Result.bind, ``Result.IsPartial.bind_explicit), (``Result.guard, ``Result.IsPartial.guard),
    (``Result.tryWith, ``Result.IsPartial.tryWith), (``Result.handle, ``Result.IsPartial.handle),
    (``Result.orElse, ``Result.IsPartial.orElse), (``Result.andAlso, ``Result.IsPartial.andAlso),
    (`Lynx.Term.Bitstring.extract, `Lynx.Result.IsPartial.extract)]
  stronger := some ("_pure", ``Result.IsPure.isPartial)

-- Core's guard fallthroughs are applied lambdas. Abstract their continuation
-- before beta reduction duplicates it into every match alternative.
private def shareStep (predicate : Predicate) : TacticM Unit :=
  liftMetaTactic fun goal => goal.withContext do
    let target := (← instantiateMVars (← goal.getType)).consumeMData
    unless target.isAppOfArity predicate.name 2 do throwError "not a purity goal"
    let .app body next := target.appArg!.consumeMData | throwError "not an applied continuation"
    -- Typed continuation wrappers add applications before the shared lambda.
    -- Reduce that prefix without substituting the continuation into its body.
    let body := body.consumeMData.headBeta
    unless body.isLambda do throwError "not a shared lambda"
    let applicable ← forallTelescopeReducing (← inferType next) fun args result =>
      return args.size == 1 && result.isAppOfArity ``Result 1
    unless applicable do throwError "not a result continuation"
    let proof ← mkAppM predicate.shared #[next, body]
    goal.apply proof

private def lemmaName (function : Name) (suffix : String) : Name :=
  function.getPrefix ++ Name.mkSimple (function.getString! ++ suffix)

/-- Realizes a lemma generated on demand, given its name. Set once the
definitions are recorded, below. -/
private initialize realizeHook : IO.Ref (Name → MetaM Bool) ← IO.mkRef fun _ => pure false

/-- Whether a lemma exists, realizing it if it is generated on demand. -/
private def realizeLemma (name : Name) : MetaM Bool := do
  if (← getEnv).contains name then return true
  discard <| (← realizeHook.get) name
  return (← getEnv).contains name

/-- The generated lemma for a full function application, if any. -/
private def functionLemma (predicate : Predicate) (head computation : Expr) :
    MetaM (Option Expr) := do
  let name := head.constName!
  unless computation.getAppNumArgs == (← getConstInfo name).type.getForallArity do return none
  let applied (suffix : String) :=
    mkAppN (mkConst (lemmaName name suffix) head.constLevels!) computation.getAppArgs
  if ← realizeLemma (lemmaName name predicate.suffix) then return some (applied predicate.suffix)
  if let some (suffix, implication) := predicate.stronger then
    if ← realizeLemma (lemmaName name suffix) then
      return some (← mkAppM implication #[applied suffix])
  return none

-- Inspect the syntax before applying purity lemmas. Blind `apply`/`intro` can
-- unfold the predicate and execute an entire computation just to reject a rule.
private def structuralStep (predicate : Predicate) : TacticM Unit :=
  liftMetaTactic fun goal => goal.withContext do
    let target := (← instantiateMVars (← goal.getType)).consumeMData
    if target.isForall then
      let (_, next) ← goal.intro1
      return [next]
    unless target.isAppOfArity predicate.name 2 do throwError "not a purity goal"
    let computation := target.appArg!.consumeMData
    let head := computation.getAppFn.consumeMData
    if head.isConst then
      let name := head.constName!
      if let some proof ← functionLemma predicate head computation then
        goal.assign proof
        return []
      if predicate.terminals.contains name then
        goal.assign (mkConst ``True.intro)
        return []
      if let some (_, rule) := predicate.rules.find? (·.1 == name) then
        return ← goal.apply (← mkConstWithFreshMVarLevels rule)
      if name == ``Pure.pure then
        let reduced ← whnf computation
        if reduced == computation then throwError "pure instance did not reduce"
        return [← goal.change (mkApp target.appFn! reduced)]
    match computation with
    | .letE _ _ value body _ =>
      return [← goal.change (mkApp target.appFn! (body.instantiate1 value))]
    | .app (.lam _ _ body _) value =>
      return [← goal.change (mkApp target.appFn! (body.instantiate1 value))]
    | _ =>
      -- Fixed-point unfoldings apply the body to all its parameters at once.
      if head.isLambda then
        return [← goal.change (mkApp target.appFn! computation.headBeta)]
      throwError "not a structural purity step"

/-- Close a goal only through a generated lemma or a terminal constructor,
leaving binds to rules that retain their successful-return equations. -/
private def lemmaStep (predicate : Predicate) : TacticM Unit :=
  liftMetaTactic fun goal => goal.withContext do
    let target := (← instantiateMVars (← goal.getType)).consumeMData
    unless target.isAppOfArity predicate.name 2 do throwError "not a purity goal"
    let computation := target.appArg!.consumeMData
    let head := computation.getAppFn.consumeMData
    unless head.isConst do throwError "not a function application"
    if let some proof ← functionLemma predicate head computation then
      goal.assign proof
      return []
    if predicate.terminals.contains head.constName! then
      goal.assign (mkConst ``True.intro)
      return []
    throwError "no generated lemma"

elab "lynx_pure_share" : tactic => shareStep purePredicate
elab "lynx_pure_step" : tactic => structuralStep purePredicate
elab "lynx_partial_share" : tactic => shareStep partialPredicate
elab "lynx_partial_step" : tactic => structuralStep partialPredicate
elab "lynx_partial_lemma" : tactic => lemmaStep partialPredicate

/-- Abstract closed tuple literals, such as lookup tables, so that proof steps
never traverse their entries. Function lemmas hold for any argument. -/
elab "lynx_generalize_tables" : tactic => do
  let rec loop (fuel : Nat) : TacticM Unit := do
    let some table := (← instantiateMVars (← getMainTarget)).find? fun value =>
        value.isAppOfArity ``Term.tuple 1 && !value.hasFVar && !value.hasLooseBVars &&
          !value.hasMVar
      | return
    liftMetaTactic fun goal => do
      let (_, next) ← goal.generalize #[{ expr := table, xName? := some `table }]
      return [next]
    match fuel with
    | 0 => return
    | fuel + 1 => loop fuel
  loop 64

private def isResultType (type : Expr) : MetaM Bool := do
  return (← whnf type).isAppOfArity ``Result 1

private def pureDefinitionId (declaration : TSyntax `command) : Command.CommandElabM Syntax := do
  let inner := declaration.raw.getArg 1
  unless inner.getKind == ``Lean.Parser.Command.definition do
    throwErrorAt declaration "#lynx_pure requires `def` declarations"
  let declId := inner.getArg 1
  let id := if declId.isIdent then declId else declId.getArg 0
  unless id.isIdent do
    throwErrorAt declId "could not determine the definition name"
  return id

private def predicateType (predicate : Predicate) (function : Name) : MetaM Expr := do
  let info ← getConstInfo function
  let functionExpr := mkConst function (info.levelParams.map Level.param)
  forallTelescopeReducing info.type fun arguments resultType => do
    unless ← isResultType resultType do
      throwError "#lynx_pure requires a definition returning `Result`"
    let proposition ← mkAppM predicate.name
      #[mkAppN functionExpr arguments]
    mkForallFVars arguments proposition

private def checkProof (predicate : Predicate) (proof : Expr) : MetaM Unit := do
  if proof.hasSorry then
    throwError "{predicate.command} could not prove {predicate.property}; refusing an incomplete proof"

private def addTheorem (name function : Name) (type proof : Expr) : CoreM Unit := do
  let info ← getConstInfo function
  addDecl <| Declaration.thmDecl {
    name := name
    levelParams := info.levelParams
    type := type
    value := proof
  }

/-- Eagerly generated lemmas are simp rules, which also discharge purity
conditions while preprocessing later well-founded definitions. -/
private def registerProof (predicate : Predicate) (function : Name) (type proof : Expr) :
    Command.CommandElabM Unit := do
  let theoremName := lemmaName function predicate.suffix
  Command.liftCoreM <| addTheorem theoremName function type proof
  Command.elabCommand (← `(attribute [simp↓, wf_preprocess] $(mkIdent theoremName)))

private def elabProof (proof : TSyntax `term) (type : Expr) : TermElabM Expr := do
  let proof ← Term.elabTermEnsuringType proof type
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars proof

private def rule (predicate : Predicate) (name : String) : Name :=
  predicate.name ++ Name.mkSimple name

/-- Structural proof steps for a definition body, given its predicate. -/
private def bodySteps (predicate : Predicate) : TermElabM (TSyntax `tactic) :=
  if predicate.name == ``Result.IsPartial then
    `(tactic| (lynx_generalize_tables; repeat' first
      | lynx_partial_share
      | lynx_partial_step
      | split
      | simp_all))
  else
    `(tactic| repeat' first
      | lynx_pure_share
      | lynx_pure_step
      | split
      | simp_all)

/-- Admissibility of `fun f => ∀ x₁ … xₙ, (f x₁ … xₙ).IsPartial`, built one
argument at a time so that unification never abstracts an application. -/
private partial def partialAdmissibility : Nat → TermElabM (TSyntax `term)
  | 0 => `(Lynx.Result.admissible_isPartial)
  | arity + 1 => do
    let inner ← partialAdmissibility arity
    let arguments := (List.range arity).toArray.map fun i => mkIdent (Name.mkSimple s!"x{i}")
    let termType := mkIdent ``Lynx.Term
    let functionType ← arguments.foldrM (fun _ result => `($termType → $result)) (← `(Result))
    let motive ← `(fun _ (function : $functionType) => ∀ $arguments:ident*,
      Result.IsPartial (function $arguments*))
    `(Lean.Order.admissible_pi_apply (P := $motive) (fun _ => $inner))

/-- Whether a definition is a partial fixed point. Its induction principle is a
reserved name, realized on demand. -/
private def isFixpoint (function : Name) : CoreM Bool := do
  try
    discard <| realizeGlobalConstNoOverload (mkIdent (function ++ `fixpoint_induct))
    pure true
  catch _ => pure false

private def arityOf (function : Name) : MetaM Nat := do
  forallTelescopeReducing (← getConstInfo function).type fun args _ => pure args.size

/-- Prove partiality of a partial fixed point, which may belong to a mutual
group, through its induction principle. The bottom is exhausted, so partiality
is admissible, and each unfolding preserves it given the recursive calls.
Parameters passed unchanged to every recursive call are fixed: the principle
takes them before its motives, which range over the remaining parameters. -/
private def fixpointProof (function : Name) (arity : Nat) : TermElabM (TSyntax `term) := do
  unless ← isFixpoint function do throwError "{function} is not a partial fixed point"
  let fixpoint := function ++ `fixpoint_induct
  -- Read the fixed binders, every motive's arity, and the parameter positions of
  -- the fixed and varying arguments in the conclusion `motive (fun ys => f args)`.
  let (fixedPositions, varyingPositions, motives) ←
    forallTelescope (← inferType (← mkConstWithLevelParams fixpoint)) fun binders conclusion => do
      let mut fixedBinders : Array Expr := #[]
      let mut motives : Array (Name × Nat) := #[]
      for binder in binders do
        let declaration ← binder.fvarId!.getDecl
        if declaration.userName.toString.startsWith "motive" then
          -- A motive's argument is a function of the varying parameters.
          let varying ← forallTelescope (← whnf declaration.type).bindingDomain! fun args _ =>
            pure args.size
          motives := motives.push (declaration.userName, varying)
        else if motives.isEmpty then
          fixedBinders := fixedBinders.push binder
      lambdaTelescope (← etaExpand conclusion.appArg!.consumeMData) fun ys body => do
        let args := body.headBeta.getAppArgs
        let position (value : Expr) : Option Nat := args.findIdx? (· == value)
        let fixed := fixedBinders.filterMap position
        let varying := ys.filterMap position
        unless fixed.size == fixedBinders.size && varying.size == ys.size &&
            fixed.size + varying.size == arity do
          throwError "unexpected fixed point induction principle for {function}"
        return (fixed, varying, motives)
  let parameters := (List.range arity).toArray.map fun i => mkIdent (Name.mkSimple s!"_pure_arg_{i}")
  let fixedArgs := fixedPositions.map (parameters[·]!)
  let varyingArgs := varyingPositions.map (parameters[·]!)
  let termType := mkIdent ``Lynx.Term
  let mut named : Array (TSyntax ``Parser.Term.namedArgument) := #[]
  let mut admissible : Array (TSyntax `term) := #[]
  for (name, varying) in motives do
    let arguments := (List.range varying).toArray.map fun i => mkIdent (Name.mkSimple s!"x{i}")
    let functionType ← arguments.foldrM (fun _ result => `($termType → $result)) (← `(Result))
    let motive ← `(fun (function : $functionType) => ∀ $arguments:ident*,
      Result.IsPartial (function $arguments*))
    named := named.push (← `(Parser.Term.namedArgument| ($(mkIdent name):ident := $motive)))
    admissible := admissible.push (← partialAdmissibility varying)
  let steps ← motives.mapM fun _ => `(?_)
  let introduce ← if parameters.isEmpty then `(tactic| skip)
    else `(tactic| intro $parameters:ident*)
  `(by
    $introduce:tactic
    refine $(mkIdent fixpoint):ident $fixedArgs:ident* $named:namedArgument* $admissible*
      $steps* $varyingArgs:ident*
    all_goals
      intros
      lynx_generalize_tables
      repeat' first
        | lynx_partial_share
        | lynx_partial_step
        | apply_assumption (config := { exfalso := false })
        | split
        | simp_all)

/-- How a definition's lemma is proved. -/
private inductive Method where
  /-- A non-recursive body, proved structurally. -/
  | body
  /-- A partial fixed point, proved through its fixed-point induction. -/
  | fixpoint
  /-- A recursive group, proved jointly through its induction principle. The
  functions are in declaration order, and the guard rule handles their clauses. -/
  | group (functions : Array Name) (guard : Name)
  deriving Inhabited

/-- Prove the predicate for a definition that is not part of a recursive group. -/
private def singleProof (predicate : Predicate) (function : Name) (method : Method) :
    TermElabM Expr := do
  let type ← predicateType predicate function
  let arity ← arityOf function
  let functionId := mkIdent function
  -- Introduce exactly the function parameters: an unbounded `intros` also
  -- reduces the predicate's computation while looking for another binder.
  let parameters := (List.range arity).toArray.map fun i => mkIdent (Name.mkSimple s!"_pure_arg_{i}")
  let introduce ← if parameters.isEmpty then `(tactic| skip)
    else `(tactic| intro $parameters:ident*)
  let steps ← bodySteps predicate
  let proofSyntax ← match method with
    | .fixpoint =>
      unless predicate.name == ``Result.IsPartial do
        throwError "a partial fixed point cannot be proved pure"
      fixpointProof function arity
    | _ =>
      `(by
        $introduce:tactic
        delta $functionId:ident
        -- Peel binds before simplifying their continuations. Simplifying a large
        -- straight-line computation first can duplicate all later branches at
        -- each intermediate match (notably binary64 conversion code).
        $steps:tactic)
  let proof ← elabProof proofSyntax type
  checkProof predicate proof
  return proof

/-- A recursive group in the equation compiler's order, which its induction
theorem uses for motives and conjunction projections, with the position of each
function's fixed parameters. -/
private structure Group where
  functions : Array Name
  perms : Array (Array (Option Nat))
  numFixed : Nat

private def groupLayout (declared : Array Name) : MetaM Group := do
  let env ← getEnv
  let (functions, perms) : Array Name × Option FixedParamPerms :=
    if let some info := Structural.eqnInfoExt.find? env declared[0]! then
      (info.declNames, some info.fixedParamPerms)
    else if let some info := WF.eqnInfoExt.find? env declared[0]! then
      (info.declNames, some info.fixedParamPerms)
    else (declared, none)
  unless functions.size == declared.size && functions.all declared.contains do
    throwError "mutual block must be a single recursive group"
  -- Parameters passed unchanged by every recursive call are fixed: the
  -- induction principle takes them first, and its motives range over the rest.
  let perms ← functions.mapIdxM fun i function => do
    let arity ← arityOf function
    let perm := (perms.bind (·.perms[i]?)).getD (Array.replicate arity none)
    unless perm.size == arity do throwError "unexpected fixed parameters for {function}"
    pure perm
  return { functions, perms, numFixed := (perms[0]!.filter Option.isSome).size }

/-- The conjunction of the predicate for every function in a group, over shared
fixed parameters. -/
private def jointType (predicate : Predicate) (group : Group) : MetaM Expr := do
  let termType := mkConst ``Lynx.Term
  withLocalDeclsDND ((List.range group.numFixed).toArray.map fun k =>
      (Name.mkSimple s!"fixed{k}", termType)) fun fixed => do
    let parts ← group.functions.mapIdxM fun i function => do
      let info ← getConstInfo function
      forallTelescopeReducing info.type fun arguments _ => do
        let args := arguments.mapIdx fun j argument =>
          match group.perms[i]![j]! with
          | some k => fixed[k]!
          | none => argument
        let varying := (arguments.zip group.perms[i]!).filterMap fun (argument, perm) =>
          if perm.isNone then some argument else none
        let proposition ← mkAppM predicate.name
          #[mkAppN (mkConst function (info.levelParams.map Level.param)) args]
        mkForallFVars varying proposition
    mkForallFVars fixed (parts.toList.dropLast.foldr (mkApp2 (mkConst ``And)) parts.back!)

/-- Prove the predicate for a recursive group through its induction principle. -/
private def jointProof (predicate : Predicate) (group : Group) (guard : Name) :
    TermElabM Expr := do
  let functions := group.functions
  let type ← jointType predicate group
  let guard := mkIdent guard
  let tryWith := mkIdent (rule predicate "tryWith")
  let handle := mkIdent (rule predicate "handle")
  -- Keep successful-return equations, so impossible returns close branches.
  let bind := mkIdent (rule predicate "bind_return")
  let bindExplicit := mkIdent (rule predicate "bind_return_explicit")
  let extract := mkIdent (rule predicate "extract")
  let lemmaStep ← if predicate.name == ``Result.IsPartial then `(tactic| lynx_partial_lemma)
    else `(tactic| fail)
  let shareStep ← if predicate.name == ``Result.IsPartial then `(tactic| lynx_partial_share)
    else `(tactic| lynx_pure_share)
  let inductionName := functions[0]! ++
    if functions.size == 1 then `induct else `mutual_induct
  let induction := mkIdent inductionName
  -- Rewrite with the equations: in other modules, `unfold` can expose the
  -- internal definition of a well-founded mutual group instead.
  let unfoldings ← functions.mapM fun function =>
    `(tactic| rw [$(mkIdent (function ++ `eq_def)):ident])
  let fixed := (List.range group.numFixed).toArray.map fun k => mkIdent (Name.mkSimple s!"fixed{k}")
  let introduce ← if fixed.isEmpty then `(tactic| skip) else `(tactic| intro $fixed:ident*)
  -- The principle takes the fixed parameters its cases use before its
  -- motives, named after the first function's parameters.
  discard <| realizeGlobalConstNoOverload induction
  let leading ← forallTelescope (← inferType (← mkConstWithLevelParams inductionName))
    fun binders _ => do
      let names ← binders.mapM fun binder => return (← binder.fvarId!.getDecl).userName
      return names.toList.takeWhile (!·.toString.startsWith "motive")
  let parameterNames ← forallTelescopeReducing (← getConstInfo functions[0]!).type
    fun arguments _ => arguments.mapM fun argument => return (← argument.fvarId!.getDecl).userName
  let fixedArgs ← leading.toArray.mapM fun name => do
    let some position := parameterNames.findIdx? (· == name) |
      throwError "unexpected fixed parameter {name} in {inductionName}"
    let some (some k) := group.perms[0]![position]? |
      throwError "unexpected fixed parameter {name} in {inductionName}"
    pure fixed[k]!
  let proofSyntax ← `(by
    $introduce:tactic
    apply $induction:ident $fixedArgs:ident*
    all_goals
      intros
      -- Unfold only the goal: recursive hypotheses may themselves be matches
      -- (for example under a shared guard continuation).
      first $[| $unfoldings:tactic]*
      repeat' first
        | $shareStep:tactic
        | $lemmaStep:tactic
        | apply $guard:ident
        | apply $tryWith:ident
        | apply $handle:ident
        | apply $bind:ident
        | apply $bindExplicit:ident
        | apply $extract:ident
        | (intro)
        -- Shared continuations and recursive calls follow from hypotheses.
        -- Matching them reducibly avoids unfolding the extractions they mention.
        | (solve | with_reducible (apply_assumption -exfalso -symm <;> assumption))
        | split
        -- Goal-only simplification closes calls with purity lemmas without
        -- also rewriting the induction hypotheses, as `grind` and `simp_all` do.
        | (solve | simp)
        | (solve | grind)
        | split at *
        | simp_all)
  let proof ← elabProof proofSyntax type
  checkProof predicate proof
  return proof

/-- One function's lemma, projected from the joint proof of its group. -/
private def memberProof (predicate : Predicate) (group : Group) (i : Nat) (joint : Expr) :
    MetaM Expr := do
  forallTelescopeReducing (← predicateType predicate group.functions[i]!) fun arguments _ => do
    let fixed := (List.range group.numFixed).toArray.map fun k =>
      arguments[(group.perms[i]!.findIdx? (· == some k)).get!]!
    let mut part := mkAppN joint fixed
    for _ in [:i] do part ← mkAppM ``And.right #[part]
    if i + 1 < group.functions.size then part ← mkAppM ``And.left #[part]
    let varying := (arguments.zip group.perms[i]!).filterMap fun (argument, perm) =>
      if perm.isNone then some argument else none
    mkLambdaFVars arguments (mkAppN part varying)

/-! ### Lemmas generated on demand

When importers can unfold a definition, the commands only record how to prove
each lemma, unless `lynx.lazyPurity` is disabled. Its reserved name is realized when first used: by a reference, by the purity steps
of a caller, or by the simprocs below. Recursive groups realize one joint proof
for their members. Realizations run in the environment of the definition, using
its recorded heartbeat limit, so they do not depend on where they are requested. -/

register_option lynx.lazyPurity : Bool := {
  defValue := true
  descr := "generate `#lynx_pure` and `#lynx_partial` lemmas when first used. \
    Eager lemmas are also simp rules for preprocessing well-founded recursion, \
    which the runtime library needs for the operations other definitions call."
}

private structure Entry where
  function : Name
  isPartial : Bool
  method : Method
  maxHeartbeats : Nat
  deriving Inhabited

private initialize entriesExt : SimplePersistentEnvExtension Entry (NameMap Entry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun entries entry => entries.insert entry.function entry
    addImportedFn := fun modules => modules.foldl (init := {}) fun entries module =>
      module.foldl (init := entries) fun entries entry => entries.insert entry.function entry
    -- Realizations hide the entries of the group they prove.
    asyncMode := .local
  }

private def predicateOf (isPartial : Bool) : Predicate :=
  if isPartial then partialPredicate else purePredicate

/-- The recorded definition whose lemma has the given name. -/
private def lemmaEntry? (env : Lean.Environment) (name : Name) : Option Entry := do
  let .str namespace_ string := name | none
  let entries := entriesExt.getState env
  let find (isPartial : Bool) : Option Entry := do
    let suffix := (predicateOf isPartial).suffix
    guard (string.endsWith suffix)
    let entry ← entries.find? (.str namespace_ (string.dropEnd suffix.length).toString)
    guard (entry.isPartial == isPartial)
    pure entry
  find false <|> find true

private def withRecordedOptions (entry : Entry) (x : MetaM α) : MetaM α :=
  withTheReader Core.Context (fun ctx =>
    let options := ctx.options
      |> (maxHeartbeats.set · entry.maxHeartbeats)
      |> (maxRecDepth.set · 100000)
      |> (Meta.synthInstance.maxSize.set · 4096)
      |> (Meta.synthInstance.maxHeartbeats.set · 400000)
    { ctx with
      options := options
      maxRecDepth := 100000
      maxHeartbeats := entry.maxHeartbeats * 1000 }) x

/-- Prove a group without its own recorded lemmas: importers record them, and
realizing them from the group's recursive calls would wait on this proof. -/
private def withoutEntries (functions : Array Name) (x : MetaM α) : MetaM α := do
  modifyEnv fun env => entriesExt.modifyState env fun entries => functions.foldl .erase entries
  x

private def realizeEntry (entry : Entry) : MetaM Unit := do
  let predicate := predicateOf entry.isPartial
  let name := lemmaName entry.function predicate.suffix
  match entry.method with
  | .group declared guard =>
    -- Realizations are enabled for the first function last, so its environment
    -- has the whole group, and each realization may request the joint proof.
    let leader := (← groupLayout declared).functions[0]!
    let joint := lemmaName leader (predicate.suffix ++ "_group")
    realizeConst leader name <| withRecordedOptions entry do
      realizeConst leader joint <| withRecordedOptions entry <| withoutEntries declared do
        let group ← groupLayout declared
        let proof ← (jointProof predicate group guard).run'
        addTheorem joint leader (← jointType predicate group) proof
      let group ← groupLayout declared
      let some i := group.functions.idxOf? entry.function |
        throwError "{entry.function} is not part of its recursive group"
      let info ← getConstInfo leader
      let proof ← memberProof predicate group i (mkConst joint (info.levelParams.map Level.param))
      addTheorem name entry.function (← predicateType predicate entry.function) proof
  | method =>
    realizeConst entry.function name <| withRecordedOptions entry <|
        withoutEntries #[entry.function] do
      let proof ← (singleProof predicate entry.function method).run'
      addTheorem name entry.function (← predicateType predicate entry.function) proof

private def reservedLemma (env : Lean.Environment) (name : Name) : Bool :=
  (lemmaEntry? env name).isSome

initialize
  registerReservedNamePredicate reservedLemma
  registerReservedNameAction fun name => do
    let some entry := lemmaEntry? (← getEnv) name | return false
    MetaM.run' (realizeEntry entry)
    return true
  realizeHook.set fun name => do
    let some entry := lemmaEntry? (← getEnv) name | return false
    realizeEntry entry
    return true

/-- Environments created while importing the module that registers the reserved
name predicate miss it, so recording definitions installs it when missing. -/
private def installReservedNames (example_ : Name) : CoreM Unit := do
  unless isReservedName (← getEnv) example_ do
    modifyEnv (reservedNamePredicatesExt.modifyState · (·.push reservedLemma))

/-- Close purity goals for translated calls with their lemmas, realizing them
on demand. Eagerly generated lemmas are also simp rules. -/
private def purityProc (predicate : Predicate) : Simp.Simproc := fun e => do
  unless e.isAppOfArity predicate.name 2 do return .continue
  let computation := (← instantiateMVars e.appArg!).consumeMData
  let head := computation.getAppFn.consumeMData
  unless head.isConst do return .continue
  let some proof ← functionLemma predicate head computation | return .continue
  return .done { expr := mkConst ``True, proof? := some (← mkEqTrue proof) }

simproc ↓ lynxIsPure (Result.IsPure _) := purityProc purePredicate
simproc ↓ lynxIsPartial (Result.IsPartial _) := purityProc partialPredicate

/-- Record or prove the lemmas of elaborated definitions. A recursive group gets
one joint proof, from which each function's lemma is projected. -/
private def generate (predicate : Predicate) (declaration : TSyntax `command)
    (methods : Array (Name × Method)) : Command.CommandElabM Unit := do
  for (function, _) in methods do
    discard <| Command.liftTermElabM <| predicateType predicate function
  -- Realizations in other modules unfold the definitions, which needs their
  -- bodies to be exported. Lemmas about hidden bodies are proved here instead.
  let exports := (← getEnv).setExporting true
  let exported := methods.all fun (function, _) =>
    match exports.find? function with
    | some (.defnInfo _) => true
    | _ => false
  if exported && lynx.lazyPurity.get (← getOptions) then
    let maxHeartbeats := maxHeartbeats.get (← getOptions)
    for (function, method) in methods do
      modifyEnv (entriesExt.addEntry · {
        function, method, maxHeartbeats
        isPartial := predicate.name == ``Result.IsPartial })
      Command.liftCoreM <| installReservedNames (lemmaName function predicate.suffix)
    return
  let mut joints : Std.HashMap Name Expr := {}
  for (function, method) in methods do
    let type ← Command.liftTermElabM <| predicateType predicate function
    match method with
    | .group declared guard =>
      let group ← Command.liftTermElabM <| withRef declaration <| groupLayout declared
      let joint ← match joints[declared[0]!]? with
        | some joint => pure joint
        | none => Command.liftTermElabM <| jointProof predicate group guard
      joints := joints.insert declared[0]! joint
      let some i := group.functions.idxOf? function |
        throwError "{function} is not part of its recursive group"
      registerProof predicate function type
        (← Command.liftTermElabM <| memberProof predicate group i joint)
    | method =>
      registerProof predicate function type
        (← Command.liftTermElabM <| singleProof predicate function method)

/-- Elaborate translated definitions and prove the predicate for each fully
applied computation. Mutually recursive definitions are proved together using
their generated mutual induction principle. Lemmas about exported bodies are
generated on demand; the others are proved immediately and are simp rules. -/
private def elaborateWith (predicate : Predicate) (doc? : Option (TSyntax ``Parser.Command.docComment))
    (declaration : TSyntax `command) : Command.CommandElabM Unit := do
  if let `(mutual $declarations:command* end) := declaration then
    if doc?.isSome then
      throwErrorAt declaration "place documentation on the definitions inside the mutual block"
    if declarations.isEmpty then throwErrorAt declaration "empty mutual block"
    let ids ← declarations.mapM pureDefinitionId
    Command.elabCommand declaration
    let functions ← ids.mapM resolveGlobalConstNoOverload
    if predicate.name == ``Result.IsPartial && (← Command.liftCoreM <| isFixpoint functions[0]!) then
      generate predicate declaration (functions.map (·, .fixpoint))
      return
    -- Check the group now, rather than when its lemmas are first used.
    discard <| Command.liftTermElabM <| withRef declaration <| groupLayout functions
    let guard := rule predicate "guard"
    generate predicate declaration (functions.map (·, .group functions guard))
    return
  if let some doc := doc? then
    unless declaration.raw.getArg 0 |>.getArg 0 |>.isNone do
      throwErrorAt doc "declaration has two documentation comments"
  let declaration : TSyntax `command := match doc? with
    | some doc =>
        let modifiers := declaration.raw.getArg 0
        let modifiers := modifiers.setArg 0 (mkNullNode #[doc.raw])
        ⟨declaration.raw.setArg 0 modifiers⟩
    | none => declaration
  let id ← pureDefinitionId declaration
  Command.elabCommand declaration
  let function ← resolveGlobalConstNoOverload id
  let fixpoint ← Command.liftCoreM <| isFixpoint function
  let method ← if fixpoint then
      unless predicate.name == ``Result.IsPartial do
        throwError "a partial fixed point cannot be proved pure"
      pure .fixpoint
    else if ← Command.liftCoreM (isRecursiveDefinition function) then
      pure (.group #[function] (rule predicate "guard_cases"))
    else pure .body
  generate predicate declaration #[(function, method)]

elab doc?:(docComment)? "#lynx_pure " declaration:command : command =>
  elaborateWith purePredicate doc? declaration

/-- Like `#lynx_pure`, for definitions that may not return: their termination
suffixes or cutoffs make them exhausted on some inputs. Each generated
`<name>_partial` theorem states that the definition makes no runtime requests. -/
elab doc?:(docComment)? "#lynx_partial " declaration:command : command =>
  -- Partial fixed points unfold whole bodies at once, and translated bodies can
  -- have hundreds of binds and matches. The limit bounds elaboration only.
  -- Admissibility of many-argument functions also needs nested order instances.
  let options (opts : Options) : Options :=
    let opts := maxRecDepth.set opts 100000
    let opts := Meta.synthInstance.maxSize.set opts 4096
    Meta.synthInstance.maxHeartbeats.set opts 400000
  Command.withScope (fun scope => { scope with opts := options scope.opts }) do
    elaborateWith partialPredicate doc? declaration

end Lynx.Purity
