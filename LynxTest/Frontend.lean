module

import all Lynx.Frontend
import Lynx
import Lean

open Lean

-- The readable fixture is the expected output of JSON-to-syntax conversion.
run_cmd do
  let request ← IO.FS.readFile "LynxTest/Frontend/sum.json"
  let .ok decoded ← Lynx.Frontend.decode request | throwError "could not decode sum.json"
  unless decoded.diagnostics.isEmpty && decoded.files.size == 1 do
    throwError "unexpected input diagnostics: {decoded.diagnostics}"
  let some file := decoded.files[0]? | throwError "missing sum file"
  let rendered ← file.commands.mapM fun cmd => do
    return (← Elab.Command.liftCoreM (PrettyPrinter.ppCommand cmd)).pretty 100
  let actual := "module\n\nimport Lynx\n\n" ++ String.intercalate "\n\n" rendered.toList ++ "\n"
  let expected ← IO.FS.readFile "LynxTest/Frontend/sum.lean"
  unless actual == expected do
    throwError "sum.json does not match sum.lean:\n{actual}"
  let result ← Lynx.Frontend.elaborate decoded
  unless result.diagnostics.isEmpty do
    throwError "sum.json failed elaboration: {result.diagnostics}"
  let some (_, env) := result.files[0]? | throwError "missing elaborated sum file"
  for name in [`sum_1, `sum_1_pure] do
    let some (_, info) := env.constants.toList.find? (fun (n, _) => privateToUserName n == name)
      | throwError "missing declaration {name}"
    unless (info.value? (allowOpaque := true)).any (fun value => !value.hasSorry) do
      throwError "{name} contains sorry"
