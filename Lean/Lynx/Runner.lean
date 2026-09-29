module

import Lynx
import Lean

/-! JSON runner for verification and Lean source rendering. Positions are one-based Unicode character positions.
Every syntax node requires `span`: `[]`, `[line]`, or `[line, column]`.
Nodes without a location inherit the enclosing location, if any. Line-only spans
never imply a diagnostic column. Names use Lean identifiers, including quoted components such as `«+/2»`.

`verify` returns `{"status": "ok" | "error", "diagnostics": [...]}`.
`render` returns `{"status": "ok", "files": {...}}`, mapping original source paths to Lean source.
Each newline-delimited request includes `"command": "verify" | "render"`.
The runner responds to each request and continues until stdin closes.
Invalid input and runner failures return `{"status": "failure", "message": "..."}`.
Each verification diagnostic has `file`, `kind` (error/warning/info), and `message`, with `line` and
`column` included only when known.
Input files are an ordered array of {file, module, imports, contents} objects.
Files are elaborated in the supplied dependency order, sharing declarations but
not local scopes or messages. Each file's definitions live in its module namespace.
Imports may name other input modules or compiled Lean modules loaded from disk.
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

private abbrev DecodeM := ReaderT Lean.Environment (StateT (Array Span) (Except String))

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

private def identifier (value : String) : DecodeM (TSyntax `ident) := do
  let stx ← Parser.runParserCategory (← read) `term value
  unless stx.isIdent do throw s!"invalid identifier '{value}'"
  return mkIdent stx.getId

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
  let name ← identifier name
  unless name.getId.getPrefix == .anonymous do throw "parameter must be an unqualified identifier"
  return withSpan (← span map j info).info name

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
    -- Erlang integers may be negative (for example the pattern in `f(-1) -> ...`).
    -- Lean has no negative numeric literal token, so `-n` becomes `(-n)`, which
    -- elaborates both as an `Int` term and as an `Int` match pattern.
    let value ← (← field j "value").getInt?
    let literal : TSyntax `num := Syntax.mkNumLit (toString value.natAbs)
    if value < 0 then
      pure (Unhygienic.run `((-$literal)))
    else
      pure ⟨literal⟩
  | "string" => do
    fields j ["kind", "value", "span"]
    pure ⟨Syntax.mkStrLit (← str j "value")⟩
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
    unless (← str inner "kind") ∈ ["def", "mutual"] do throw "lynx_pure must wrap def or mutual"
    let decl ← command map inner info
    pure (Unhygienic.run `(#lynx_pure $decl:command))
  | "mutual" => do
    fields j ["kind", "defs", "span"]
    let defs ← arr j "defs"
    if defs.isEmpty then throw "mutual requires at least one definition"
    let decls ← defs.mapM fun decl => do
      unless (← str decl "kind") == "def" do throw "mutual requires def declarations"
      command map decl info
    pure (Unhygienic.run `(mutual $decls:command* end))
  | "def" => do
    fields j ["kind", "name", "params", "body", "span"]
    let name ← str j "name"
    let name ← identifier name
    unless name.getId.getPrefix == .anonymous do throw "definition name must be unqualified"
    let params ← (← arr j "params").mapM (param map info)
    let termType := mkIdent ``Lynx.Term
    let resultType := mkIdent ``Lynx.Result
    let binders := params.map fun p => Unhygienic.run `(bracketedBinder| ($p : $termType))
    let body ← term map info false (← field j "body")
    pure (Unhygienic.run `(public def $name $binders:bracketedBinder* : $resultType := $body))
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
    let mut messages : MessageLog := {}
    for cmd in commands do
      Elab.Command.elabCommandTopLevel cmd
      messages := messages ++ (← get).messages
    modify fun state => { state with messages }
  let (_, state) ← (action.run { fileName := file, fileMap := map, snap? := none, cancelTk? := none }).run
    (Elab.Command.mkState env {} (Options.empty.setBool `Elab.async false)) |>.toIO
      (fun _ => IO.userError "runner elaboration failed")
  return state

/-- One input file, decoded directly to Lean commands without elaboration. -/
structure DecodedFile where
  fileName : String
  moduleName : String
  imports : Array String
  fileMap : FileMap
  commands : Array (TSyntax `command)
  private spans : Array Span

/-- Decode input files after the selected command requests them. -/
private def decode (files : Array Json) (env : Lean.Environment) : IO (Array DecodedFile) := do
  files.mapM fun entry => do
    let file ← IO.ofExcept (str entry "file")
    try
      let map := FileMap.ofString (← IO.FS.readFile file)
      let (moduleName, imports, commands, spans) ← IO.ofExcept do
        fields entry ["file", "module", "imports", "contents"]
        let moduleName ← str entry "module"
        let namespaceId ← (identifier moduleName).run env |>.run' #[]
        let imports ← (← arr entry "imports").mapM fun j => do
          let name ← j.getStr?
          let _ ← (identifier name).run env |>.run' #[]
          pure name
        let (commands, spans) ← (← arr entry "contents").mapM (command map) |>.run env |>.run #[]
        let start := Unhygienic.run `(namespace $namespaceId)
        let stop := Unhygienic.run `(end $namespaceId)
        pure (moduleName, imports, #[start] ++ commands ++ #[stop], spans)
      return ⟨file, moduleName, imports, map, commands, spans⟩
    catch err => throw (IO.userError s!"{file}: {err}")

/-- Render syntax without elaborating the input declarations. -/
private def render (files : Array DecodedFile) (env : Lean.Environment) : IO (UInt32 × Json) := do
  let sources ← files.mapM fun file => do
    let action : CoreM String := do
      let commands ← file.commands.mapM fun cmd => do
        return (← PrettyPrinter.ppCommand cmd).pretty 100
      let imports := file.imports.toList.map ("import " ++ ·)
      return "module\n\n" ++ String.intercalate "\n" ("public import Lynx" :: imports) ++
        "\n\n" ++ String.intercalate "\n\n" commands.toList ++ "\n"
    let source ← (action.run' { fileName := file.fileName, fileMap := file.fileMap }
      { env := env }).toIO (fun _ => IO.userError s!"{file.fileName}: Lean source rendering failed")
    return (file.fileName, toJson source)
  return (0, Json.mkObj [("status", toJson "ok"), ("files", Json.mkObj sources.toList)])

/-- Verify in input order, retaining declarations while resetting per-file state. -/
private def verify (files : Array DecodedFile) (env : Lean.Environment) : IO (UInt32 × Json) := do
  let mut imports : Array Import := #[{ module := `Lynx }]
  for file in files do
    for name in file.imports do
      if name == file.moduleName || !files.any (·.moduleName == name) then
        let id ← IO.ofExcept <| (identifier name).run env |>.run' #[]
        unless imports.any (·.module == id.getId) do
          imports := imports.push { module := id.getId }
  unsafe enableInitializersExecution
  let env ← importModules imports {} (loadExts := true)
  let mut diagnostics := #[]
  let mut failed := false
  let mut env := env
  for file in files do
    let state ← elaborateFile env file.fileName file.fileMap file.commands
    env := state.env
    for msg in state.messages.toList do
      if msg.severity == .error then failed := true
      diagnostics := diagnostics.push (diagnostic file.fileName
        (match msg.severity with | .error => "error" | .warning => "warning" | .information => "info")
        (← msg.data.toString) (messageLocation file.fileMap file.spans msg))
  return (if failed then 1 else 0, Json.mkObj [
    ("status", toJson (if failed then "error" else "ok")), ("diagnostics", .arr diagnostics)])

private def runFiles (j : Json)
    (action : Array DecodedFile → Lean.Environment → IO (UInt32 × Json)) : IO Json := do
  let files ← IO.ofExcept do
    fields j ["command", "version", "files"]
    arr j "files"
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := `Lynx }] {} (loadExts := true)
  return (← action (← decode files env) env).2

private def run (request : String) : IO Json := do
  try
    let j ← IO.ofExcept (Json.parse request)
    let command ← IO.ofExcept (str j "command")
    let version ← IO.ofExcept (str j "version")
    unless version == "1.0" do throw (IO.userError "unsupported version")
    match command with
    | "verify" => runFiles j verify
    | "render" => runFiles j render
    | _ => throw (IO.userError s!"unsupported runner command '{command}'")
  catch err =>
    return Json.mkObj [("status", toJson "failure"), ("message", toJson err.toString)]

end Lynx.Runner

/-- Process newline-delimited JSON requests until stdin closes. -/
public def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    let stdin ← IO.getStdin
    let stdout ← IO.getStdout
    repeat
      let request ← stdin.getLine
      if request.isEmpty then break
      stdout.putStrLn (← Lynx.Runner.run request).compress
      stdout.flush
    return 0
  | _ =>
    IO.println (Lean.Json.mkObj [("status", Lean.toJson "failure"),
      ("message", Lean.toJson "usage: Runner.lean")]).compress
    return 2
