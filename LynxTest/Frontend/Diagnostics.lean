module

import all Lynx.Frontend
import Lean

open Lean

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def response (request : String) (expected : String) : IO Json := do
  let decoded ← IO.ofExcept (← Lynx.Frontend.decode request)
  check decoded.diagnostics.isEmpty s!"unexpected input diagnostics: {decoded.diagnostics}"
  let result ← Lynx.Frontend.elaborate decoded
  let json := result.toJson
  check ((json.getObjValAs? String "status").toOption == some expected) json.pretty
  return json

private def unknownRequest (location : Option Json) : String := Id.run do
  let node := json% {kind: "def", name: "test_0", params: [],
    body: {kind: "ident", name: "unknown", span: []}}
  let node := match location with | none => node | some loc => node.setObjVal! "span" loc
  return (json% {version: "1.0", files: {"LynxTest/Frontend/sum.erl": [$node]}}).compress

-- Unknown, line-only, and precise locations remain distinct in diagnostics.
#eval do
  for (span, line, column) in #[
      (some (json% []), none, none),
      (some (json% [1]), some 1, none),
      (some (json% [3]), some 3, none),
      (some (json% [4, 18]), some 4, some 18)] do
    let result ← response (unknownRequest span) "error"
    let diagnostics ← IO.ofExcept (result.getObjValAs? (Array Json) "diagnostics")
    check (diagnostics.any fun d =>
      (d.getObjValAs? String "kind").toOption == some "error" &&
      (d.getObjValAs? String "file").toOption == some "LynxTest/Frontend/sum.erl" &&
      (d.getObjValAs? Nat "line").toOption == line &&
      (d.getObjValAs? Nat "column").toOption == column) result.pretty

-- Invalid positions are rejected, including zero-based lines and columns.
#eval do
  for span in #[json% [0], json% [1, 0], json% [999], json% [3, 999], json% [1, 2, 3]] do
    let .ok decoded ← Lynx.Frontend.decode (unknownRequest (some span))
      | throw (IO.userError "expected a per-file input error")
    check (decoded.files.isEmpty && decoded.diagnostics.size == 1) s!"accepted invalid span {span}"
  let .ok missing ← Lynx.Frontend.decode (unknownRequest none)
    | throw (IO.userError "expected a per-file input error")
  check (missing.files.isEmpty && missing.diagnostics.size == 1) "accepted missing span"
  check ((← Lynx.Frontend.decode "{").toOption.isNone) "accepted malformed JSON"
  let map := FileMap.ofString "αβ\nγ"
  let (span, _) ← IO.ofExcept ((Lynx.Frontend.span map (json% {span: [1, 2]})).run #[])
  check (span.info == SourceInfo.synthetic ⟨2⟩ ⟨4⟩ true) "incorrect Unicode offsets"

-- Nested errors use the application span; duplicate names in separate files
-- succeed because every file is elaborated in its own environment.
#eval do
  let request ← IO.FS.readFile "LynxTest/Frontend/sum.json"
  let _ ← response request "ok"
  let bad ← response (request.replace "Lynx.Modules.Erlang.add_2" "Lynx.Modules.Erlang.unknown_2") "error"
  let diagnostics ← IO.ofExcept (bad.getObjValAs? (Array Json) "diagnostics")
  check (diagnostics.any fun d =>
    (d.getObjValAs? Nat "line").toOption == some 4 &&
    (d.getObjValAs? Nat "column").toOption == some 18) bad.pretty
  let request ← IO.ofExcept (Json.parse request)
  let files ← IO.ofExcept (request.getObjVal? "files")
  let nodes ← IO.ofExcept (files.getObjVal? "LynxTest/Frontend/sum.erl")
  let files := files.setObjVal! "LynxTest/Frontend/./sum.erl" nodes
  let _ ← response (request.setObjVal! "files" files).compress "ok"
  pure ()
