-- Proof automation shared by the Base64 and hex laws. Loaded by `prelude`.
meta section
namespace MonotonicityTactics
open Lean Meta Elab Tactic

/-- Fold a closed tuple literal into a local definition before simplifying.
This keeps large OTP lookup tables out of the simplifier's traversal and lets
its discrimination tree match lookup lemmas against the local definition. -/
elab "lynx_fold_tuple " table:ident : tactic => do
  liftMetaTactic fun goal => goal.withContext do
    let declaration ← getLocalDeclFromUserName table.getId
    unless declaration.isLet do throwError "expected a local tuple definition"
    let target ← goal.getType
    let literals ← IO.mkRef (#[] : Array Expr)
    target.forEach' fun value => do
      if value.isAppOfArity ``Lynx.Term.tuple 1 &&
          !value.hasFVar && !value.hasLooseBVars then
        literals.modify (·.push value)
        return false
      return true
    let literals ← literals.get
    let mut matching := #[]
    for value in literals do
      if ← isDefEq value declaration.toExpr then matching := matching.push value
    if matching.isEmpty then throwError "no definitionally equal tuple literal in the goal"
    let target := target.replace fun value =>
      if matching.contains value then some declaration.toExpr else none
    return [← goal.change target]

/-- Keep shared Core fallthroughs abstract while relating two computations. -/
elab "lynx_mono_share" : tactic => do
  liftMetaTactic fun goal => goal.withContext do
    let target := (← instantiateMVars (← goal.getType)).consumeMData
    unless target.isAppOf ``Lean.Order.PartialOrder.rel do throwError "not a relation goal"
    let args := target.getAppArgs
    let .app leftBody leftNext := args[args.size-2]!.consumeMData |
      throwError "not a shared continuation"
    let .app rightBody rightNext := args.back!.consumeMData |
      throwError "not a shared continuation"
    unless leftNext.consumeMData.headBeta.isLambda && rightNext.consumeMData.headBeta.isLambda do
      throwError "continuations are already abstract"
    let leftBody := leftBody.consumeMData.headBeta
    let rightBody := rightBody.consumeMData.headBeta
    unless leftBody.isLambda && rightBody.isLambda do throwError "not shared bodies"
    let relation := mkAppN target.getAppFn (args.extract 0 (args.size-2))
    goal.apply (← mkAppM ``Lynx.Result.rel_shared
      #[relation, leftNext, rightNext, leftBody, rightBody])

/-- Select monotonicity rules by syntax before unification can evaluate a result. -/
elab "lynx_mono_step" : tactic => do
  liftMetaTactic fun goal => goal.withContext do
    let target := (← instantiateMVars (← goal.getType)).consumeMData
    unless target.isAppOf ``Lean.Order.PartialOrder.rel do throwError "not a relation goal"
    for declaration in ← getLCtx do
      if !declaration.isImplementationDetail &&
          declaration.type.consumeMData.isAppOfArity ``And 2 then
        return (← goal.cases declaration.fvarId).toList.map (·.mvarId)
    let args := target.getAppArgs
    let left := args[args.size-2]!.consumeMData.headBeta
    let right := args.back!.consumeMData.headBeta
    if left == right then
      return ← goal.apply (← mkConstWithFreshMVarLevels ``Lean.Order.PartialOrder.rel_refl)
    if (← whnf (← inferType left)).isForall then
      let (_, next) ← goal.intro1
      return [next]
    if left != args[args.size-2]! || right != args.back! then
      let args := (args.set! (args.size-2) left).set! (args.size-1) right
      return [← goal.change (mkAppN target.getAppFn args)]
    let head := left.getAppFn.consumeMData
    unless head.isConst do throwError "not a computation constructor"
    let name := head.constName!
    if name == ``Bind.bind || name == ``Lynx.Result.bind then
      unless right.isAppOf ``Bind.bind || right.isAppOf ``Lynx.Result.bind do
        throwError "the right side is not a bind"
      let leftArgs := left.getAppArgs
      let rightArgs := right.getAppArgs
      unless leftArgs.size ≥ 2 && rightArgs.size ≥ 2 do
        throwError "expected fully applied binds"
      let rule ← if leftArgs[leftArgs.size-2]! == rightArgs[rightArgs.size-2]! then
          pure ``Lynx.Result.bind_mono_pure
        else if leftArgs.back! == rightArgs.back! then pure ``Lynx.Result.bind_mono_left
        else throwError "both sides of this bind vary"
      return ← goal.apply (← mkConstWithFreshMVarLevels rule)
    if name == ``Lynx.Term.Bitstring.extract then
      return ← goal.apply (← mkConstWithFreshMVarLevels ``Lynx.Term.Bitstring.extract_mono)
    if name == ``Lynx.Result.tryWith || name == ``Lynx.Result.guard then
      return ← goal.apply (← mkConstWithFreshMVarLevels ``Lynx.Result.tryWith_mono_pure)
    throwError "no monotonicity rule for this computation"

end MonotonicityTactics
end
