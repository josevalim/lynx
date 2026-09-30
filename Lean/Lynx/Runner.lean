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
Function tables carry entry metadata: body, captures, args, pure, and span.
The decoder builds typed pure/effectful callables; a pure entry must prove
the translated body's purity during elaboration. Each entry also generates checked
application equations for standalone calls and binds. Pure calls preserve depth;
effectful calls consume one level and retain the caller's depth in continuations.
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
  | "wildcard" => do
    fields j ["kind", "span"]
    unless pattern do throw "wildcard is only valid in patterns"
    pure (Unhygienic.run `(_))
  | "ident" => do
    fields j ["kind", "name", "span"]
    pure ⟨(← identifier (← str j "name")).raw⟩
  | "integer" => do
    fields j ["kind", "value", "span"]
    let value ← (← field j "value").getInt?
    pure ⟨← Parser.runParserCategory (← read) `term (toString value)⟩
  | "string" => do
    fields j ["kind", "value", "span"]
    pure ⟨Syntax.mkStrLit (← str j "value")⟩
  | "array" => do
    fields j ["kind", "elements", "span"]
    let elements ← (← arr j "elements").mapM (term map info pattern)
    pure (Unhygienic.run `(#[$elements,*]))
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
    fields j ["kind", "expressions", "cases", "span"]
    let exprs ← (← arr j "expressions").mapM (term map info false)
    if exprs.isEmpty then throw "match requires at least one expression"
    let cases ← (← arr j "cases").mapM fun c => do
      fields c ["patterns", "body", "span"]
      let ci ← span map c info
      let pats ← (← arr c "patterns").mapM (term map ci true)
      unless pats.size == exprs.size do throw "match case must have one pattern per expression"
      let body ← term map ci false (← field c "body")
      pure (withSpan ci.info (Unhygienic.run `(Lean.Parser.Term.matchAltExpr| | $pats,* => $body)))
    if cases.isEmpty then throw "match requires at least one case"
    pure (Unhygienic.run `(match $[$exprs:term],* with $cases:matchAlt*))
  | _ => throw s!"unsupported {if pattern then "pattern" else "term"} kind '{kind}'"
  return withSpan info.info result

private structure TableEntry where
  captures : Array (TSyntax `ident)
  arguments : Array (TSyntax `ident)
  body : TSyntax `term
  adapter : TSyntax `term
  isPure : Bool

private def tableEntry (map : FileMap) (info : Span) (entry : Json) : DecodeM TableEntry := do
  fields entry ["body", "captures", "args", "pure", "span"]
  let entryInfo ← span map entry info
  let captureIds ← (← arr entry "captures").mapM (param map entryInfo)
  let argumentIds ← (← arr entry "args").mapM (param map entryInfo)
  let captures := captureIds.map fun id => (⟨id.raw⟩ : TSyntax `term)
  let arguments := argumentIds.map fun id => (⟨id.raw⟩ : TSyntax `term)
  let body ← term map entryInfo false (← field entry "body")
  let isPure ← (← field entry "pure").getBool?
  let toExcept := mkIdent ``Lynx.Result.toExcept
  let exceptError := mkIdent ``Except.error
  let resultError := mkIdent ``Lynx.Result.error
  let exceptionError := mkIdent ``Lynx.Exception.error
  let atom := mkIdent ``Lynx.Term.atom
  let capturesId := mkIdent `captures
  let argsId := mkIdent `args
  let adapter ← if isPure then
    pure (Unhygienic.run `(fun $capturesId:ident $argsId:ident =>
      match $capturesId:ident, $argsId:ident with
      | #[$captures,*], #[$arguments,*] => $toExcept $body (by simp)
      | _, _ => $exceptError ($exceptionError ($atom "badarg"))))
  else
    pure (Unhygienic.run `(fun $capturesId:ident $argsId:ident =>
      match $capturesId:ident, $argsId:ident with
      | #[$captures,*], #[$arguments,*] => $body
      | _, _ => $resultError ($exceptionError ($atom "badarg"))))
  return ⟨captureIds, argumentIds, body, withSpan entryInfo.info adapter, isPure⟩

private partial def command (map : FileMap) (j : Json) (parent : Span := {}) : DecodeM (TSyntax `command) := do
  let info ← span map j parent
  let kind ← str j "kind"
  let result ← match kind with
  | "command" => do
    fields j ["kind", "name", "expr", "span"]
    let name ← str j "name"
    unless name == "lynx_pure" do throw "unsupported command name"
    let inner ← field j "expr"
    unless (← str inner "kind") ∈ ["def", "mutual"] do throw "lynx_pure must wrap def or mutual"
    let decl ← command map inner info
    pure (Unhygienic.run `(#lynx_pure $decl:command))
  | "fun_table" => do
    fields j ["kind", "name", "entries", "span"]
    let name ← identifier (← str j "name")
    unless name.getId.getPrefix == .anonymous do throw "table name must be unqualified"
    let entries ← (← arr j "entries").mapM fun entry => do
      let entry ← tableEntry map info entry
      let ctor := mkIdent (if entry.isPure then ``Lynx.Term.FunEntry.pure else ``Lynx.Term.FunEntry.effectful)
      pure (Unhygienic.run `($ctor $(entry.adapter)))
    let body := Unhygienic.run `(#[$entries,*])
    let tableType := mkIdent ``Lynx.Term.FunTable
    pure (Unhygienic.run `(public def $name : $tableType := $body))
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

/-- Table metadata also gives kernel-checked application equations for both pure
and effectful entries, so proofs can simplify translated `Term.apply` calls
without inspecting the table or duplicating callback implementations. Pure calls
preserve depth; effectful bodies consume one level while their caller's
continuation retains its original depth. -/
private def commands (map : FileMap) (j : Json) : DecodeM (Array (TSyntax `command)) := do
  let declaration ← command map j
  if (← str j "kind") != "fun_table" then return #[declaration]
  let info ← span map j
  let table ← identifier (← str j "name")
  let entries ← arr j "entries"
  let mut result := #[declaration]
  for index in [:entries.size] do
    let entry ← tableEntry map info entries[index]!
    let name := mkIdent (Name.mkSimple s!"{table.getId.getString!}_apply_{index}_bind")
    let callName := mkIdent (Name.mkSimple s!"{table.getId.getString!}_apply_{index}")
    let termType := mkIdent ``Lynx.Term
    let resultType := mkIdent ``Lynx.Result
    let resolve := mkIdent ``Lynx.Result.resolve
    let apply := mkIdent ``Lynx.Term.apply
    let function := mkIdent ``Lynx.Term.function
    let binders := (entry.captures ++ entry.arguments).map fun id =>
      Unhygienic.run `(bracketedBinder| ($id : $termType))
    let captures := entry.captures.map fun id => (⟨id.raw⟩ : TSyntax `term)
    let arguments := entry.arguments.map fun id => (⟨id.raw⟩ : TSyntax `term)
    let parameters := captures ++ arguments
    let bindOk := mkIdent ``Lynx.Result.bind_ok
    let resolvePure := mkIdent ``Lynx.Result.resolve_of_isPure
    let pureOk := mkIdent ``Lynx.Result.isPure_ok
    let id : TSyntax `term := ⟨Syntax.mkNumLit (toString index)⟩
    let arity : TSyntax `term := ⟨Syntax.mkNumLit (toString arguments.size)⟩
    let body := entry.body
    let adapter := entry.adapter
    let alpha := mkIdent `α
    let depth := mkIdent `depth
    let next := mkIdent `next
    let value := mkIdent `value
    let natType := mkIdent ``Nat
    let ok := mkIdent ``Lynx.Result.ok
    let lemma ← if entry.isPure then
      let reduce := mkIdent ``Lynx.Result.resolve_apply_pure
      let ofExcept := mkIdent ``Lynx.Result.ofExcept
      let toExcept := mkIdent ``Lynx.Result.toExcept
      let cancel := mkIdent ``Lynx.Result.ofExcept_toExcept
      pure (Unhygienic.run `(@[simp↓] public theorem $name {$alpha:ident : Type} ($depth:ident : $natType)
        $binders:bracketedBinder* ($next:ident : $termType → $resultType $alpha:ident) :
        $resolve $table $depth:ident ($apply ($function $id $arity #[$captures,*]) #[$arguments,*] >>= $next:ident) =
          $resolve $table $depth:ident ($body >>= $next:ident) := by
        rw [$reduce $table $depth:ident $id $arity #[$captures,*] #[$arguments,*] $adapter $next:ident
          (by rfl) (by rfl)]
        change $resolve $table $depth:ident ($ofExcept ($toExcept $body (by simp)) >>= $next:ident) = _
        rw [$cancel $body]))
    else
      let reduce := mkIdent ``Lynx.Result.resolve_apply_effectful
      let resolveBind := mkIdent ``Lynx.Result.resolve_bind
      pure (Unhygienic.run `(@[simp↓] public theorem $name {$alpha:ident : Type} ($depth:ident : $natType)
        $binders:bracketedBinder* ($next:ident : $termType → $resultType $alpha:ident) :
        $resolve $table ($depth:ident + 1) ($apply ($function $id $arity #[$captures,*]) #[$arguments,*] >>= $next:ident) =
          ($resolve $table $depth:ident $body >>= fun $value:ident => $resolve $table ($depth:ident + 1) ($next:ident $value:ident)) := by
        rw [$resolveBind $table ($depth:ident + 1)
          ($apply ($function $id $arity #[$captures,*]) #[$arguments,*]) $next:ident, $reduce $table $depth:ident $id $arity #[$captures,*] #[$arguments,*] $adapter
          (by rfl) (by rfl)]
        rfl))
    result := result.push (withSpan info.info lemma)
    -- Simp indexes explicit Result.bind separately from the monadic notation.
    let explicitName := mkIdent (Name.mkSimple s!"{table.getId.getString!}_apply_{index}_bind_explicit")
    let bind := mkIdent ``Lynx.Result.bind
    let explicitLemma ← if entry.isPure then
      pure (Unhygienic.run `(@[simp↓] public theorem $explicitName {$alpha:ident : Type} ($depth:ident : $natType)
        $binders:bracketedBinder* ($next:ident : $termType → $resultType $alpha:ident) :
        $resolve $table $depth:ident ($bind ($apply ($function $id $arity #[$captures,*]) #[$arguments,*]) $next:ident) =
          $resolve $table $depth:ident ($bind $body $next:ident) := by
        exact $name $depth:ident $parameters* $next:ident))
    else
      pure (Unhygienic.run `(@[simp↓] public theorem $explicitName {$alpha:ident : Type} ($depth:ident : $natType)
        $binders:bracketedBinder* ($next:ident : $termType → $resultType $alpha:ident) :
        $resolve $table ($depth:ident + 1) ($bind ($apply ($function $id $arity #[$captures,*]) #[$arguments,*]) $next:ident) =
          $bind ($resolve $table $depth:ident $body) (fun $value:ident => $resolve $table ($depth:ident + 1) ($next:ident $value:ident)) := by
        exact $name $depth:ident $parameters* $next:ident))
    result := result.push (withSpan info.info explicitLemma)
    let reduction ← if entry.isPure then
      pure (Unhygienic.run `(@[simp] public theorem $callName ($depth:ident : $natType)
        $binders:bracketedBinder* :
        $resolve $table $depth:ident ($apply ($function $id $arity #[$captures,*]) #[$arguments,*]) = $body := by
        simpa only [($bindOk), ($resolvePure $table $depth:ident $body (by simp))] using $name $depth:ident $parameters* (fun $value:ident => $ok $value:ident)))
    else
      pure (Unhygienic.run `(@[simp] public theorem $callName ($depth:ident : $natType)
        $binders:bracketedBinder* :
        $resolve $table ($depth:ident + 1) ($apply ($function $id $arity #[$captures,*]) #[$arguments,*]) =
          $resolve $table $depth:ident $body := by
        simpa only [($bindOk), ($resolvePure), ($pureOk)] using $name $depth:ident $parameters* (fun $value:ident => $ok $value:ident)))
    result := result.push (withSpan info.info reduction)
  return result

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
  private reexportImports : Bool

/-- Decode input files after the selected command requests them. -/
private def decode (files : Array Json) (env : Lean.Environment) : IO (Array DecodedFile) := do
  files.mapM fun entry => do
    let file ← IO.ofExcept (str entry "file")
    try
      let moduleName ← IO.ofExcept (str entry "module")
      let source ← if moduleName == "Erlang.program" then pure "" else IO.FS.readFile file
      let map := FileMap.ofString source
      let (moduleName, imports, commands, spans, reexportImports) ← IO.ofExcept do
        fields entry ["file", "module", "imports", "contents"]
        let namespaceId ← (identifier moduleName).run env |>.run' #[]
        let imports ← (← arr entry "imports").mapM fun j => do
          let name ← j.getStr?
          let _ ← (identifier name).run env |>.run' #[]
          pure name
        let contents ← arr entry "contents"
        let reexportImports := contents.any fun j =>
          match str j "kind" with
          | .ok kind => kind == "fun_table"
          | .error _ => false
        let (commands, spans) ← contents.mapM (commands map) |>.run env |>.run #[]
        let start := Unhygienic.run `(namespace $namespaceId)
        let stop := Unhygienic.run `(end $namespaceId)
        pure (moduleName, imports, #[start] ++ commands.flatten ++ #[stop], spans, reexportImports)
      return ⟨file, moduleName, imports, map, commands, spans, reexportImports⟩
    catch err => throw (IO.userError s!"{file}: {err}")

/-- Render syntax without elaborating the input declarations. -/
private def render (files : Array DecodedFile) (env : Lean.Environment) : IO (UInt32 × Json) := do
  let sources ← files.mapM fun file => do
    let action : CoreM String := do
      let commands ← file.commands.mapM fun cmd => do
        return (← PrettyPrinter.ppCommand cmd).pretty 100
      -- Public application equations mention the entry bodies in their types.
      let importPrefix := if file.reexportImports then "public import " else "import "
      let imports := file.imports.toList.map (importPrefix ++ ·)
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
