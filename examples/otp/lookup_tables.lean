-- Lookup table helpers shared by the Base64 and hex laws. Loaded by `prelude`.
meta section
namespace LookupTables
open Lean Meta Elab Tactic

/-- Translation shares large literals, such as OTP lookup tables, through
module definitions. -/
def isTable (value : Expr) : Bool :=
  value.isConst && value.constName!.getString!.startsWith "lynx_literal_"

/-- Fold a shared lookup table into a local definition, so simp's
discrimination tree matches lookup lemmas stated about the local definition. -/
elab "lynx_fold_table " table:ident : tactic => do
  liftMetaTactic fun goal => goal.withContext do
    let declaration ← getLocalDeclFromUserName table.getId
    unless declaration.isLet do throwError "expected a local table definition"
    let target ← goal.getType
    let literals ← IO.mkRef (#[] : Array Expr)
    target.forEach' fun value => do
      if isTable value then
        literals.modify (·.push value)
        return false
      return true
    let literals ← literals.get
    let mut matching := #[]
    for value in literals do
      if ← isDefEq value declaration.toExpr then matching := matching.push value
    if matching.isEmpty then throwError "no definitionally equal table in the goal"
    let target := target.replace fun value =>
      if matching.contains value then some declaration.toExpr else none
    return [← goal.change target]

end LookupTables
end
