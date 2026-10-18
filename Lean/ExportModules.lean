module

import Lean

/-! Emit the public Erlang runtime functions.
Run from Lean/: lake env lean --run ExportModules.lean > modules.json
Pure functions return `Except Exception Term`; the others return `Result`.
-/

open Lean

/-- Whether a function type ends in `Except`, after all its parameters. -/
private def returnsExcept : Expr → Bool
  | .forallE _ _ body _ => returnsExcept body
  | type => type.isAppOf ``Except

private def manifest (env : Environment) : Json := Id.run do
  let exports := env.setExporting true
  let mut modules : Std.TreeMap String (List (String × Json)) := {}
  for (name, info) in env.constants.toList do
    unless name.getPrefix.getPrefix == `Erlang &&
        (exports.find? name).isSome && !isMarkedMeta env name do continue
    unless info matches .defnInfo _ do continue
    let function := name.getString!
    -- Only Erlang functions carry an arity; supporting declarations do not.
    unless (function.splitOn "/").getLast!.toNat?.isSome do continue
    let pure := returnsExcept info.type
    let entry := (function, Json.mkObj [("pure", toJson pure)])
    let moduleName := name.getPrefix.getString!
    modules := modules.insert moduleName (entry :: modules.getD moduleName [])
  return Json.mkObj <| modules.toList.map fun (name, functions) =>
    (name, Json.mkObj (functions.mergeSort (fun a b => a.1 < b.1)))

public def main : IO Unit := do
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := `Lynx.Modules.Erlang.erlang }, { module := `Lynx.Modules.Erlang.lists },
    { module := `Lynx.Modules.Erlang.maps }, { module := `Lynx.Modules.Erlang.math },
    { module := `Lynx.Modules.Erlang.erts_internal }]
    {} (loadExts := true)
  IO.println (manifest env).pretty
