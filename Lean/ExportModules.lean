module

import Lean

/-! Emit the public Erlang runtime functions.
Run from Lean/: lake env lean --run ExportModules.lean > modules.json
Purity means that `#lynx_pure` has generated a proof for the function.
-/

open Lean

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
    let proof := Name.str name.getPrefix (function ++ "_pure")
    let pure := match env.find? proof with
      | some (.thmInfo _) => true
      | _ => false
    let entry := (function, Json.mkObj [("pure", toJson pure)])
    let moduleName := name.getPrefix.getString!
    modules := modules.insert moduleName (entry :: modules.getD moduleName [])
  return Json.mkObj <| modules.toList.map fun (name, functions) =>
    (name, Json.mkObj (functions.mergeSort (fun a b => a.1 < b.1)))

public def main : IO Unit := do
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := `Erlang.erlang }, { module := `Erlang.maps }]
    {} (loadExts := true)
  IO.println (manifest env).pretty
