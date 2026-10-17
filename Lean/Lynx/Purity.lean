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
    (``Result.handle, ``Result.IsPure.handle)]

private def partialPredicate : Predicate where
  name := ``Result.IsPartial
  command := "#lynx_partial"
  property := "partiality"
  suffix := "_partial"
  terminals := [``Result.ok, ``Result.error, ``Result.exhausted]
  shared := ``Result.IsPartial.shared
  rules := [(``Bind.bind, ``Result.IsPartial.bind),
    (``Result.bind, ``Result.IsPartial.bind_explicit), (``Result.guard, ``Result.IsPartial.guard),
    (``Result.tryWith, ``Result.IsPartial.tryWith), (``Result.handle, ``Result.IsPartial.handle)]
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

/-- The generated lemma for a function application, if any. -/
private def functionLemma (predicate : Predicate) (head computation : Expr) :
    MetaM (Option Expr) := do
  let name := head.constName!
  let lemma (suffix : String) := name.getPrefix ++ Name.mkSimple (name.getString! ++ suffix)
  let applied (suffix : String) := mkAppN (mkConst (lemma suffix) head.constLevels!) computation.getAppArgs
  if (← getEnv).contains (lemma predicate.suffix) then return some (applied predicate.suffix)
  if let some (suffix, implication) := predicate.stronger then
    if (← getEnv).contains (lemma suffix) then
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

private def predicateType (predicate : Predicate) (function : Name) :
    Command.CommandElabM Expr := do
  let info ← getConstInfo function
  let functionExpr := mkConst function (info.levelParams.map Level.param)
  Command.liftTermElabM do
    forallTelescopeReducing info.type fun arguments resultType => do
      unless ← isResultType resultType do
        throwError "#lynx_pure requires a definition returning `Result`"
      let proposition ← mkAppM predicate.name
        #[mkAppN functionExpr arguments]
      mkForallFVars arguments proposition

private def registerProof (predicate : Predicate) (function : Name) (type proof : Expr) :
    Command.CommandElabM Unit := do
  if proof.hasSorry then
    throwError "{predicate.command} could not prove {predicate.property}; refusing an incomplete proof"
  let info ← getConstInfo function
  let theoremName := function.getPrefix ++ Name.mkSimple (function.getString! ++ predicate.suffix)
  Command.liftCoreM <| addAndCompile <| Declaration.thmDecl {
    name := theoremName
    levelParams := info.levelParams
    type := type
    value := proof
  }
  Command.elabCommand (← `(attribute [simp↓, wf_preprocess] $(mkIdent theoremName)))

private def rule (predicate : Predicate) (name : String) : Ident :=
  mkIdent (predicate.name ++ Name.mkSimple name)

/-- Structural proof steps for a definition body, given its predicate. -/
private def bodySteps (predicate : Predicate) : Command.CommandElabM (TSyntax `tactic) :=
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
private partial def partialAdmissibility : Nat → Command.CommandElabM (TSyntax `term)
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
private def isFixpoint (function : Name) : Command.CommandElabM Bool :=
  Command.liftCoreM do
    try
      discard <| realizeGlobalConstNoOverload (mkIdent (function ++ `fixpoint_induct))
      pure true
    catch _ => pure false

/-- Prove partiality of a partial fixed point, which may belong to a mutual
group, through its induction principle. The bottom is exhausted, so partiality
is admissible, and each unfolding preserves it given the recursive calls.
Parameters passed unchanged to every recursive call are fixed: the principle
takes them before its motives, which range over the remaining parameters. -/
private def fixpointProof (function : Name) (arity : Nat) : Command.CommandElabM (TSyntax `term) := do
  unless ← isFixpoint function do throwError "{function} is not a partial fixed point"
  let fixpoint := function ++ `fixpoint_induct
  -- Read the fixed binders, every motive's arity, and the parameter positions of
  -- the fixed and varying arguments in the conclusion `motive (fun ys => f args)`.
  let (fixedPositions, varyingPositions, motives) ← Command.liftTermElabM do
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

/-- Prove the predicate for a recursive group through its induction principle,
generating one theorem per function. -/
private def proveGroup (predicate : Predicate) (declaration : TSyntax `command)
    (functions : Array Name) (guard : Ident) : Command.CommandElabM Unit := do
  -- The equation compiler can reorder a mutual group. Its induction theorem
  -- uses that order for motives and conjunction projections.
  let env ← getEnv
  let declaredFunctions := functions
  let (functions, perms) : Array Name × Option FixedParamPerms :=
    if let some info := Structural.eqnInfoExt.find? env functions[0]! then
      (info.declNames, some info.fixedParamPerms)
    else if let some info := WF.eqnInfoExt.find? env functions[0]! then
      (info.declNames, some info.fixedParamPerms)
    else (functions, none)
  unless functions.size == declaredFunctions.size && functions.all declaredFunctions.contains do
    throwErrorAt declaration "mutual block must be a single recursive group"
  let types : Array Expr ← functions.mapM (predicateType predicate)
  -- Parameters passed unchanged by every recursive call are fixed: the
  -- induction principle takes them first, and its motives range over the rest.
  let perms ← Command.liftTermElabM do
    functions.mapIdxM fun i function => do
      let arity ← forallTelescopeReducing (← getConstInfo function).type fun args _ =>
        pure args.size
      let perm := (perms.bind (·.perms[i]?)).getD (Array.replicate arity none)
      unless perm.size == arity do throwError "unexpected fixed parameters for {function}"
      pure perm
  let numFixed := (perms[0]!.filter Option.isSome).size
  let jointType ← Command.liftTermElabM do
    let termType := mkConst ``Lynx.Term
    withLocalDeclsDND ((List.range numFixed).toArray.map fun k =>
        (Name.mkSimple s!"fixed{k}", termType)) fun fixed => do
      let parts ← functions.mapIdxM fun i function => do
        let info ← getConstInfo function
        forallTelescopeReducing info.type fun arguments _ => do
          let args := arguments.mapIdx fun j argument =>
            match perms[i]![j]! with
            | some k => fixed[k]!
            | none => argument
          let varying := (arguments.zip perms[i]!).filterMap fun (argument, perm) =>
            if perm.isNone then some argument else none
          let proposition ← mkAppM predicate.name
            #[mkAppN (mkConst function (info.levelParams.map Level.param)) args]
          mkForallFVars varying proposition
      mkForallFVars fixed (parts.toList.dropLast.foldr (mkApp2 (mkConst ``And)) parts.back!)
  let tryWith := rule predicate "tryWith"
  let handle := rule predicate "handle"
  -- Keep successful-return equations, so impossible returns close branches.
  let bind := rule predicate "bind_return"
  let bindExplicit := rule predicate "bind_return_explicit"
  let lemmaStep ← if predicate.name == ``Result.IsPartial then `(tactic| lynx_partial_lemma)
    else `(tactic| fail)
  let proof ← Command.liftTermElabM do
    let inductionName := functions[0]! ++
      if functions.size == 1 then `induct else `mutual_induct
    let induction := mkIdent inductionName
    let definitions := functions.map mkIdent
    let unfoldings ← definitions.mapM fun definition => `(tactic| unfold $definition:ident)
    let fixed := (List.range numFixed).toArray.map fun k => mkIdent (Name.mkSimple s!"fixed{k}")
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
      let some (some k) := perms[0]![position]? |
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
          | $lemmaStep:tactic
          | apply $guard:ident
          | apply $tryWith:ident
          | apply $handle:ident
          | apply $bind:ident
          | apply $bindExplicit:ident
          | (intro)
          | (solve | grind)
          | split at *
          | simp_all)
    let proof ← Term.elabTermEnsuringType proofSyntax jointType
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars proof
  for i in [:functions.size] do
    let part ← Command.liftTermElabM do
      forallTelescopeReducing types[i]! fun arguments _ => do
        let fixed := (List.range numFixed).toArray.map fun k =>
          arguments[(perms[i]!.findIdx? (· == some k)).get!]!
        let mut part := mkAppN proof fixed
        for _ in [:i] do part ← mkAppM ``And.right #[part]
        if i + 1 < functions.size then part ← mkAppM ``And.left #[part]
        let varying := (arguments.zip perms[i]!).filterMap fun (argument, perm) =>
          if perm.isNone then some argument else none
        mkLambdaFVars arguments (mkAppN part varying)
    registerProof predicate functions[i]! types[i]! part

/-- Elaborate translated definitions and prove the predicate for each fully
applied computation. Mutually recursive definitions are proved together using
their generated mutual induction principle. Each generated theorem is a simp rule. -/
private def elaborateWith (predicate : Predicate) (doc? : Option (TSyntax ``Parser.Command.docComment))
    (declaration : TSyntax `command) : Command.CommandElabM Unit := do
  if let `(mutual $declarations:command* end) := declaration then
    if doc?.isSome then
      throwErrorAt declaration "place documentation on the definitions inside the mutual block"
    if declarations.isEmpty then throwErrorAt declaration "empty mutual block"
    let ids ← declarations.mapM pureDefinitionId
    Command.elabCommand declaration
    let functions ← ids.mapM resolveGlobalConstNoOverload
    if predicate.name == ``Result.IsPartial && (← isFixpoint functions[0]!) then
      for function in functions do
        let type ← predicateType predicate function
        let arity ← Command.liftTermElabM do
          forallTelescopeReducing (← getConstInfo function).type fun args _ => pure args.size
        let proofSyntax ← fixpointProof function arity
        let proof ← Command.liftTermElabM do
          let proof ← Term.elabTermEnsuringType proofSyntax type
          Term.synthesizeSyntheticMVarsNoPostponing
          instantiateMVars proof
        registerProof predicate function type proof
      return
    proveGroup predicate declaration functions (rule predicate "guard")
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
  let type ← predicateType predicate function
  let arity ← Command.liftTermElabM do
    forallTelescopeReducing (← getConstInfo function).type fun args _ => pure args.size
  let functionId := mkIdent function
  -- Introduce exactly the function parameters: an unbounded `intros` also
  -- reduces the predicate's computation while looking for another binder.
  let parameters := (List.range arity).toArray.map fun i => mkIdent (Name.mkSimple s!"_pure_arg_{i}")
  let introduce ← if parameters.isEmpty then `(tactic| skip)
    else `(tactic| intro $parameters:ident*)
  if !(← isFixpoint function) && (← Command.liftCoreM (isRecursiveDefinition function)) then
    proveGroup predicate declaration #[function] (rule predicate "guard_cases")
    return
  let steps ← bodySteps predicate
  let proofSyntax ← if ← isFixpoint function then
      unless predicate.name == ``Result.IsPartial do
        throwError "a partial fixed point cannot be proved pure"
      fixpointProof function arity
    else
      `(by
        $introduce:tactic
        delta $functionId:ident
        -- Peel binds before simplifying their continuations. Simplifying a large
        -- straight-line computation first can duplicate all later branches at
        -- each intermediate match (notably binary64 conversion code).
        $steps:tactic)
  let proof ← Command.liftTermElabM do
    let proof ← Term.elabTermEnsuringType proofSyntax type
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars proof
  registerProof predicate function type proof

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
