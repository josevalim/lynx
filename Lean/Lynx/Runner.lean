module

import Lynx
import Lean

/-! JSON runner for verification and Lean source rendering. Positions are one-based Unicode character positions.
Every syntax node requires `span`: `[]`, `[line]`, or `[line, column]`.
Nodes without a location inherit the enclosing location, if any. Line-only spans
never imply a diagnostic column. Names use dot-separated alphanumeric/underscore/apostrophe
components, beginning with a letter or underscore.

`verify` returns `{"status": "ok" | "error", "diagnostics": [...]}`.
`render` returns `{"status": "ok", "files": {...}}`, mapping original source paths to Lean source.
Invalid input and runner failures return `{"status": "failure", "message": "..."}`.
Exit codes are 0 for success, 1 for verification errors, and 2 for runner failures.
Each verification diagnostic has `file`, `kind` (error/warning/info), and `message`, with `line` and
`column` included only when known.
Files share only the fixed `Lynx` imports, never declarations or scope changes.
Library references use fully qualified names; local variables and generated
function references remain unqualified. No namespaces are opened for input files.
Verification elaborates decoded syntax directly. Rendering pretty-prints that syntax as Lean source. -/
namespace Lynx.Runner
open Lean

private def fields (j : Json) (allowed : List String) : Except String Unit := do
  let obj ← j.getObj?
  for (key, _) in obj.toArray do
    unless key ∈ allowed do throw s!"unsupported field '{key}'"

private def field (j : Json) (key : String) : Except String Json := j.getObjVal? key
private def str (j : Json) (key : String) : Except String String := do
  (← field j key).getStr?
private def arr (j : Json) (key : String) : Except String (Array Json) := do
  (← field j key).getArr?

private inductive Location where
  | unknown
  | line (line : Nat)
  | column (position : Position)

private instance : Inhabited Location := ⟨.unknown⟩

private structure Span where
  info : SourceInfo := .synthetic 0 0 true
  location : Location := .unknown

private instance : Inhabited Span := ⟨{}⟩

private abbrev DecodeM := StateT (Array Span) (Except String)

private def span (map : FileMap) (j : Json) (parent : Span := {}) : DecodeM Span := do
  let xs ← arr j "span"
  if xs.isEmpty then
    modify (·.push parent)
    return parent
  unless xs.size ≤ 2 do throw "span must be [], [line], or [line, column]"
  let line ← xs[0]!.getNat?
  let column ← if xs.size == 2 then xs[1]!.getNat? else pure 1
  unless line > 0 && column > 0 && line ≤ map.getLastLine do
    throw "span position is out of range"
  let pos := map.ofPosition ⟨line, column - 1⟩
  unless map.toPosition pos == ⟨line, column - 1⟩ do
    throw "span position is out of range"
  -- A line-only location is a zero-width anchor, not a claimed first column.
  let stop := if xs.size == 1 || pos.atEnd map.source then pos else pos.next map.source
  let result : Span := ⟨.synthetic pos stop true,
    if xs.size == 1 then .line line else .column ⟨line, column - 1⟩⟩
  modify (·.push result)
  return result

private def identifier (value : String) : Except String (TSyntax `ident) := do
  let parts := value.splitOn "."
  for part in parts do
    let chars := part.toList
    unless chars.head?.any (fun c => c.isAlpha || c == '_') &&
        chars.all (fun c => c.isAlphanum || c == '_' || c == '\'') && part != "_" do
      throw s!"invalid identifier '{value}'"
  return mkIdent (parts.foldl Name.str .anonymous)

/-- Fill quotation scaffolding only; preserve source information on spliced nodes. -/
private partial def located (info : SourceInfo) (stx : Syntax) : Syntax :=
  match stx with
  | .node old kind args => .node (if old == .none then info else old) kind (args.map (located info))
  | .atom old value => .atom (if old == .none then info else old) value
  | .ident old raw name pre => .ident (if old == .none then info else old) raw name pre
  | .missing => .missing

private def withSpan (info : SourceInfo) (stx : TSyntax k) : TSyntax k :=
  ⟨(located info stx.raw).setInfo info⟩

private def param (map : FileMap) (info : Span) (j : Json) : DecodeM (TSyntax `ident) := do
  fields j ["kind", "name", "span"]
  unless (← str j "kind") == "ident" do throw "parameter must be an identifier"
  let name ← str j "name"
  if name.contains '.' then throw "parameter must be an unqualified identifier"
  return withSpan (← span map j info).info (← identifier name)

private partial def term (map : FileMap) (parent : Span) (pattern : Bool)
    (j : Json) : DecodeM (TSyntax `term) := do
  let info ← span map j parent
  let kind ← str j "kind"
  let result ← match kind with
  | "ident" => do
    fields j ["kind", "name", "span"]
    pure ⟨(← identifier (← str j "name")).raw⟩
  | "integer" => do
    fields j ["kind", "value", "span"]
    pure ⟨Syntax.mkNumLit (toString (← (← field j "value").getNat?))⟩
  | "string" => do
    fields j ["kind", "value", "span"]
    pure ⟨Syntax.mkStrLit (← str j "value")⟩
  | "wildcard" => do
    fields j ["kind", "span"]
    unless pattern do throw "wildcard is only valid in patterns"
    pure (Unhygienic.run `(_))
  | "apply" => do
    fields j ["kind", "function", "args", "span"]
    let fnJson ← field j "function"
    if pattern && (← str fnJson "kind") != "ident" then
      throw "pattern application requires a constructor identifier"
    let fn ← term map info pattern fnJson
    let args ← (← arr j "args").mapM (term map info pattern)
    if args.isEmpty then throw "application requires at least one argument"
    pure (Unhygienic.run `($fn $args*))
  | "fun" => do
    if pattern then throw "fun is not valid in patterns"
    fields j ["kind", "params", "body", "span"]
    let params ← (← arr j "params").mapM (param map info)
    if params.isEmpty then throw "fun requires at least one parameter"
    let body ← term map info false (← field j "body")
    pure (Unhygienic.run `(fun $params:ident* => $body))
  | "match" => do
    if pattern then throw "match is not valid in patterns"
    fields j ["kind", "expression", "cases", "span"]
    let expr ← term map info false (← field j "expression")
    let cases ← (← arr j "cases").mapM fun c => do
      fields c ["pattern", "body", "span"]
      let ci ← span map c info
      let pat ← term map ci true (← field c "pattern")
      let body ← term map ci false (← field c "body")
      pure (withSpan ci.info (Unhygienic.run `(Lean.Parser.Term.matchAltExpr| | $pat => $body)))
    if cases.isEmpty then throw "match requires at least one case"
    pure (Unhygienic.run `(match $expr:term with $cases:matchAlt*))
  | _ => throw s!"unsupported {if pattern then "pattern" else "term"} kind '{kind}'"
  return withSpan info.info result

private partial def command (map : FileMap) (j : Json) (parent : Span := {}) : DecodeM (TSyntax `command) := do
  let info ← span map j parent
  let kind ← str j "kind"
  let result ← match kind with
  | "command" => do
    fields j ["kind", "name", "expr", "span"]
    unless (← str j "name") == "lynx_pure" do throw "unsupported command name"
    let inner ← field j "expr"
    unless (← str inner "kind") == "def" do throw "lynx_pure must wrap def"
    let decl ← command map inner info
    pure (Unhygienic.run `(#lynx_pure $decl:command))
  | "def" => do
    fields j ["kind", "name", "params", "body", "span"]
    let name ← str j "name"
    if name.contains '.' then throw "definition name must be unqualified"
    let name ← identifier name
    let params ← (← arr j "params").mapM (param map info)
    let termType := mkIdent ``Lynx.Term
    let resultType := mkIdent ``Lynx.Result
    let binders := params.map fun p => Unhygienic.run `(bracketedBinder| ($p : $termType))
    let body ← term map info false (← field j "body")
    pure (Unhygienic.run `(def $name $binders:bracketedBinder* : $resultType := $body))
  | _ => throw s!"unsupported command kind '{kind}'"
  return withSpan info.info result

private def diagnostic (file kind message : String) (location : Location := .unknown) : Json :=
  Json.mkObj <| [("file", toJson file), ("kind", toJson kind), ("message", toJson message)] ++
    match location with
    | .unknown => []
    | .line line => [("line", toJson line)]
    | .column pos => [("line", toJson pos.line), ("column", toJson (pos.column + 1))]

/-- Match original offsets, retaining the precision the producer actually supplied.
If ranges coincide (e.g. a column at EOF and a line-only anchor), conservatively
report the less precise location rather than inventing a column. -/
private def messageLocation (map : FileMap) (spans : Array Span) (msg : Message) : Location := Id.run do
  let mut result := Location.unknown
  for span in spans do
    if let .synthetic start stop _ := span.info then
      if map.toPosition start == msg.pos && some (map.toPosition stop) == msg.endPos then
        match span.location with
        | .unknown => return .unknown
        | .line line => return .line line
        | .column pos => result := .column pos
  return result

private def elaborateFile (env : Lean.Environment) (file : String) (map : FileMap)
    (commands : Array (TSyntax `command)) : IO Elab.Command.State := do
  let action : Elab.Command.CommandElabM Unit := do
    for cmd in commands do Elab.Command.elabCommandTopLevel cmd
  let (_, state) ← (action.run { fileName := file, fileMap := map, snap? := none, cancelTk? := none }).run
    (Elab.Command.mkState env {} (Options.empty.setBool `Elab.async false)) |>.toIO
      (fun _ => IO.userError "runner elaboration failed")
  return state

/-- One input file, decoded directly to Lean commands without elaboration. -/
structure DecodedFile where
  fileName : String
  fileMap : FileMap
  commands : Array (TSyntax `command)
  private spans : Array Span

/-- Decode the request once for either command. Invalid input aborts the request. -/
private def decode (request : String) : IO (Array DecodedFile) := do
  let files ← IO.ofExcept do
    let j ← Json.parse request
    fields j ["files", "version"]
    unless (← str j "version") == "1.0" do throw "unsupported version"
    (← field j "files").getObj?
  files.toArray.mapM fun (file, nodes) => do
    try
      let map := FileMap.ofString (← IO.FS.readFile file)
      let (commands, spans) ← IO.ofExcept do
        (← nodes.getArr?).mapM (command map) |>.run #[]
      return ⟨file, map, commands, spans⟩
    catch err => throw (IO.userError s!"{file}: {err}")

/-- Render syntax without elaborating the input declarations. -/
private def render (files : Array DecodedFile) (env : Lean.Environment) : IO (UInt32 × Json) := do
  let sources ← files.mapM fun file => do
    let action : CoreM String := do
      let commands ← file.commands.mapM fun cmd => do
        return (← PrettyPrinter.ppCommand cmd).pretty 100
      return "module\n\nimport Lynx\n\n" ++ String.intercalate "\n\n" commands.toList ++ "\n"
    let source ← (action.run' { fileName := file.fileName, fileMap := file.fileMap }
      { env := env }).toIO (fun _ => IO.userError s!"{file.fileName}: Lean source rendering failed")
    return (file.fileName, toJson source)
  return (0, Json.mkObj [("status", toJson "ok"), ("files", Json.mkObj sources.toList)])

/-- Each file is verified independently; only Lean messages become diagnostics. -/
private def verify (files : Array DecodedFile) (env : Lean.Environment) : IO (UInt32 × Json) := do
  let mut diagnostics := #[]
  let mut failed := false
  for file in files do
    let state ← elaborateFile env file.fileName file.fileMap file.commands
    for msg in state.messages.toList do
      if msg.severity == .error then failed := true
      diagnostics := diagnostics.push (diagnostic file.fileName
        (match msg.severity with | .error => "error" | .warning => "warning" | .information => "info")
        (← msg.data.toString) (messageLocation file.fileMap file.spans msg))
  return (if failed then 1 else 0, Json.mkObj [
    ("status", toJson (if failed then "error" else "ok")), ("diagnostics", .arr diagnostics)])

private def run (action : Array DecodedFile → Lean.Environment → IO (UInt32 × Json)) : IO UInt32 := do
  let (status, response) ← try
    let files ← decode (← (← IO.getStdin).getLine)
    unsafe enableInitializersExecution
    let env ← importModules #[{ module := `Lynx }] {} (loadExts := true)
    action files env
  catch err =>
    pure (2, Json.mkObj [("status", toJson "failure"), ("message", toJson err.toString)])
  IO.println response.compress
  return status

end Lynx.Runner

/-- Process one newline-delimited JSON request and write one JSON response to stdout. -/
public def main (args : List String) : IO UInt32 := do
  match args with
  | ["verify"] => Lynx.Runner.run Lynx.Runner.verify
  | ["render"] => Lynx.Runner.run Lynx.Runner.render
  | _ =>
    IO.println (Lean.Json.mkObj [("status", Lean.toJson "failure"),
      ("message", Lean.toJson "usage: Runner.lean (verify|render)")]).compress
    return 2
