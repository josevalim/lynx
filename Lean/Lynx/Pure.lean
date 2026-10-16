module

public meta import Lean
public import Lynx.Term

public meta section

/-! Generate kernel-checked purity lemmas for translated functions.
Each definition gets an ordinary `<name>_pure` theorem, registered with `simp`.
Recursive definitions use their compiler-generated induction principle. -/
namespace Lynx.Pure
open Lean Meta Elab Tactic

-- Core's guard fallthroughs are applied lambdas. Abstract their continuation
-- before beta reduction duplicates it into every match alternative.
elab "lynx_pure_share" : tactic => do
  liftMetaTactic fun goal => goal.withContext do
    let target := (← instantiateMVars (← goal.getType)).consumeMData
    unless target.isAppOfArity ``Result.IsPure 2 do throwError "not a purity goal"
    let .app body next := target.appArg!.consumeMData | throwError "not an applied continuation"
    -- Typed continuation wrappers add applications before the shared lambda.
    -- Reduce that prefix without substituting the continuation into its body.
    let body := body.consumeMData.headBeta
    unless body.isLambda do throwError "not a shared lambda"
    let applicable ← forallTelescopeReducing (← inferType next) fun args result =>
      return args.size == 1 && result.isAppOfArity ``Result 1
    unless applicable do throwError "not a result continuation"
    let proof ← mkAppM ``Result.IsPure.shared #[next, body]
    goal.apply proof

-- Inspect the syntax before applying purity lemmas. Blind `apply`/`intro` can
-- unfold IsPure and execute an entire computation just to reject a rule.
elab "lynx_pure_step" : tactic => do
  liftMetaTactic fun goal => goal.withContext do
    let target := (← instantiateMVars (← goal.getType)).consumeMData
    if target.isForall then
      let (_, next) ← goal.intro1
      return [next]
    unless target.isAppOfArity ``Result.IsPure 2 do throwError "not a purity goal"
    let computation := target.appArg!.consumeMData
    let head := computation.getAppFn.consumeMData
    if head.isConst then
      let name := head.constName!
      let proofName := name.getPrefix ++ Name.mkSimple (name.getString! ++ "_pure")
      if (← getEnv).contains proofName then
        let proof := mkAppN (mkConst proofName head.constLevels!) computation.getAppArgs
        goal.assign proof
        return []
      if name == ``Result.ok || name == ``Result.error then
        goal.assign (mkConst ``True.intro)
        return []
      let rule? := if name == ``Bind.bind then some ``Result.IsPure.bind
        else if name == ``Result.bind then some ``Result.IsPure.bind_explicit
        else if name == ``Result.tryWith then some ``Result.IsPure.tryWith
        else if name == ``Result.handle then some ``Result.IsPure.handle else none
      if let some rule := rule? then
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
    | _ => throwError "not a structural purity step"

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

private def pureType (function : Name) : Command.CommandElabM Expr := do
  let info ← getConstInfo function
  let functionExpr := mkConst function (info.levelParams.map Level.param)
  Command.liftTermElabM do
    forallTelescopeReducing info.type fun arguments resultType => do
      unless ← isResultType resultType do
        throwError "#lynx_pure requires a definition returning `Result`"
      let proposition ← mkAppM ``Result.IsPure
        #[mkAppN functionExpr arguments]
      mkForallFVars arguments proposition

private def registerPureProof (function : Name) (type proof : Expr) : Command.CommandElabM Unit := do
  if proof.hasSorry then
    throwError "#lynx_pure could not prove purity; refusing an incomplete proof"
  let info ← getConstInfo function
  let theoremName := function.getPrefix ++ Name.mkSimple (function.getString! ++ "_pure")
  Command.liftCoreM <| addAndCompile <| Declaration.thmDecl {
    name := theoremName
    levelParams := info.levelParams
    type := type
    value := proof
  }
  Command.elabCommand (← `(attribute [simp↓] $(mkIdent theoremName)))

/-- Elaborate pure definitions and prove that each fully applied computation
neither reads nor changes the environment. Mutually recursive definitions are
proved together using their generated mutual induction principle. Each generated
`<name>_pure` theorem is a simp rule. -/
private def elaboratePurity (doc? : Option (TSyntax ``Parser.Command.docComment))
    (declaration : TSyntax `command) : Command.CommandElabM Unit := do
  if let `(mutual $declarations:command* end) := declaration then
    if doc?.isSome then
      throwErrorAt declaration "place documentation on the definitions inside the mutual block"
    if declarations.isEmpty then throwErrorAt declaration "empty mutual block"
    let ids ← declarations.mapM pureDefinitionId
    Command.elabCommand declaration
    let functions ← ids.mapM resolveGlobalConstNoOverload
    let types ← functions.mapM pureType
    let jointType := types.toList.dropLast.foldr (mkApp2 (mkConst ``And)) types.back!
    let proof ← Command.liftTermElabM do
      let induction := mkIdent (functions[0]! ++ `mutual_induct)
      let definitions := functions.map mkIdent
      let proofSyntax ← `(by
        apply $induction:ident
        all_goals
          intros
          simp_all (config := { failIfUnchanged := false }) [$[$definitions:ident],*]
          repeat' first
            | apply Result.IsPure.tryWith
            | apply Result.IsPure.handle
            | apply Result.IsPure.bind
            | apply Result.IsPure.bind_explicit
            | (intro)
            | split
            | simp_all)
      let proof ← Term.elabTermEnsuringType proofSyntax jointType
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars proof
    let mut remaining := proof
    for i in [:functions.size] do
      let (part, rest) ← Command.liftTermElabM do
        if i + 1 == functions.size then return (remaining, remaining)
        return (← mkAppM ``And.left #[remaining], ← mkAppM ``And.right #[remaining])
      registerPureProof functions[i]! types[i]! part
      remaining := rest
    return
  if let some doc := doc? then
    unless declaration.raw.getArg 0 |>.getArg 0 |>.isNone do
      throwErrorAt doc "#lynx_pure declaration has two documentation comments"
  let declaration : TSyntax `command := match doc? with
    | some doc =>
        let modifiers := declaration.raw.getArg 0
        let modifiers := modifiers.setArg 0 (mkNullNode #[doc.raw])
        ⟨declaration.raw.setArg 0 modifiers⟩
    | none => declaration
  let id ← pureDefinitionId declaration
  Command.elabCommand declaration
  let function ← resolveGlobalConstNoOverload id
  let purityType ← pureType function
  let proof ← Command.liftTermElabM do
    let functionId := mkIdent function
    -- Introduce exactly the function parameters: an unbounded `intros` also
    -- reduces IsPure's computation while looking for another binder.
    let parameters ← forallTelescopeReducing (← getConstInfo function).type fun args _ =>
      pure (args.mapIdx fun i _ => mkIdent (Name.mkSimple s!"_pure_arg_{i}"))
    let introduce ← if parameters.isEmpty then `(tactic| skip)
      else `(tactic| intro $parameters:ident*)
    let induction := mkIdent (function ++ `induct)
    let proofSyntax ← if ← isRecursiveDefinition function then
      `(by
        apply $induction:ident
        all_goals
          intros
          -- Unfold only the goal: recursive hypotheses may themselves be matches
          -- (for example under a shared guard continuation).
          unfold $functionId:ident
          repeat' first
            | apply Result.IsPure.tryWith
            | apply Result.IsPure.handle
            | apply Result.IsPure.bind
            | apply Result.IsPure.bind_explicit
            | (intro)
            | split at *
            | simp_all)
    else
      `(by
        $introduce:tactic
        delta $functionId:ident
        -- Peel binds before simplifying their continuations. Simplifying a large
        -- straight-line computation first can duplicate all later branches at
        -- each intermediate match (notably binary64 conversion code).
        repeat' first
          | lynx_pure_share
          | lynx_pure_step
          | split
          | simp_all)
    let proof ← Term.elabTermEnsuringType
      proofSyntax
      purityType
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars proof
  registerPureProof function purityType proof

elab doc?:(docComment)? "#lynx_pure " declaration:command : command =>
  elaboratePurity doc? declaration

end Lynx.Pure
