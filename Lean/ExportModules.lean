module

import Lean

/-! Emit the public Erlang runtime functions.
Run from Lean/: lake env lean --run ExportModules.lean > modules.json
Purity means that `#lynx_pure` has generated a proof for the function.
Only functions of type `Lynx.Term → ... → Lynx.Result`, with one term per
arity, are exported, because the translator calls every exported function
with Erlang terms.
-/

open Lean

/-- Number of explicit `Lynx.Term` parameters when `type` has the shape
`Lynx.Term → ... → Lynx.Result`, the only calling convention the translator
emits (`Module.«name/arity» arg₁ ... argₙ`). Functions that take anything else,
such as the function table of `spawn/1` and `apply/2` or the thunks of
`andalso/2`, would produce ill-typed Lean if the translator called them. -/
private def termArity? : Expr → Option Nat
  | .forallE _ (.const `Lynx.Term []) body .default =>
      if body.hasLooseBVars then none else (termArity? body).map (· + 1)
  | .app (.const `Lynx.Result _) (.const `Lynx.Term []) => some 0
  | _ => none

private def manifest (env : Environment) : Json := Id.run do
  let exports := env.setExporting true
  let mut modules : Std.TreeMap String (List (String × Json)) := {}
  for (name, info) in env.constants.toList do
    unless name.getPrefix.getPrefix == `Erlang &&
        (exports.find? name).isSome && !isMarkedMeta env name do continue
    unless info matches .defnInfo _ do continue
    let function := name.getString!
    -- Only Erlang functions carry an arity; supporting declarations do not.
    let some arity := (function.splitOn "/").getLast!.toNat? | continue
    -- Only export functions the translator can call with Erlang terms.
    unless termArity? info.type == some arity do continue
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
  let env ← importModules #[{ module := `Erlang.erlang }, { module := `Erlang.lists },
    { module := `Erlang.maps }]
    {} (loadExts := true)
  IO.println (manifest env).pretty
