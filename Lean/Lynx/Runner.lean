module

import Lynx
import Lean

/-! JSON runner for verification and Lean source rendering. Positions are one-based Unicode character positions.
See `Runner.schema.json` for the request and response schemas.
Every syntax node requires `span`: `[]`, `[line]`, or `[line, column]`.
Nodes without a location inherit the enclosing location, if any. Line-only spans
never imply a diagnostic column. Function and variable names retain their Erlang spelling; the decoder
constructs and escapes their Lean identifiers.

Each verified file emits `{"status": "ok" | "error" | "skipped", "file": ..., "module": ...,
"source": ..., "time_ms": ..., "diagnostics": [...]}`. Time includes rendering, imports,
elaboration, auditing, and artifact writing; shared runtime loading is excluded.
Files blocked by an unsuccessful input import are skipped without elaboration.
A `{"status": "done"}` message terminates each completed request.
Each newline-delimited request includes `"command": "verify"`.
Updates are flushed as each file finishes. The runner continues until stdin closes.
Invalid input and runner failures return `{"status": "failure", "message": "..."}`.
Each verification diagnostic has `file`, `module`, nullable `declaration`, `severity`
(error/warning/information), and `message`, with `line` and `column` included only when known.
Requests include `cache_dir`; input files may include a SHA-256 `cache_key` incorporating dependencies.
Files without a key and their dependents are verified without persistent caching.
Verified artifacts are cached below `cache_dir/lean-VERSION-HASH`, using Lake’s compiled artifact hashes.
Only successful elaboration and axiom audits are cached; updates include a `cached` Boolean.
Input files are an ordered array of {file, module, imports, contents, cache_key} objects.
Theorem nodes contain name, named params, an optional requires helper, an ensures helper,
and a proof object. Helpers are ordinary Result computations called with the theorem's
parameters. An absent requires helper means no assumption.
A proof object contains tactic source, nonnegative indentation, and a span locating
the first character of that source. The producer handles host delimiters and line offsets. Proof syntax keeps
its own source ranges, mapped to the supplied host locations using a synthetic file map.
Original source files are not read.
Function tables carry entry metadata: body, captures, args, pure, and span.
The decoder builds typed pure/effectful callables; a pure entry must prove
the translated body's purity during elaboration. Each entry also generates checked
application equations for standalone calls and binds. Pure calls preserve depth;
effectful calls consume one level and retain the caller's depth in continuations.
Files are elaborated in the supplied dependency order against their declared imports.
Verified files are exported to temporary modules for importing by later files.
Each file's definitions live in its module namespace.
Module names arrive qualified by the producer, such as `Erlang.foo` or `Elixir.Foo`;
functions acquire `/arity` here.
Imports name other input modules or compiled Lean modules loaded from disk.
Erlang imports without a distinct input file resolve to Lynx.Modules.Erlang.* runtime modules.
Runtime module identities differ from their Erlang.* declaration namespaces.
Verification elaborates decoded syntax directly. Rendering pretty-prints that syntax as Lean source. -/
namespace Lynx.Runner
open Lean
open Lean.Parser.Term (doSeqItem)

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

private structure ProofDiagnostic where
  declarationName : Name
  message : String
  location : Location

private structure DecodeState where
  spans : Array Span := #[]
  diagnostics : Array ProofDiagnostic := #[]
  theorems : Array (Name × Span) := #[]

private abbrev DecodeM := ReaderT Lean.Environment (StateT DecodeState (Except String))

private def span (map : FileMap) (j : Json) (parent : Span := {}) : DecodeM Span := do
  let xs ← arr j "span"
  if xs.isEmpty then
    modify fun s => { s with spans := s.spans.push parent }
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
  modify fun s => { s with spans := s.spans.push result }
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

private def functionName (name : String) (arity : Nat) : TSyntax `ident :=
  mkIdent (Name.mkSimple s!"{name}/{arity}")

private def variableName (j : Json) : DecodeM (TSyntax `ident) := do
  let value ← field j "name"
  let name ← match value.getNat? with
    | .ok index => pure s!"_{index}"
    | .error _ => do
      let name ← value.getStr?
      pure (if name.startsWith "_" then "_v" ++ name else "v" ++ name)
  return mkIdent (Name.mkSimple name)

private def param (map : FileMap) (info : Span) (j : Json) : DecodeM (TSyntax `ident) := do
  fields j ["kind", "name", "span"]
  unless (← str j "kind") == "var" do throw "parameter must be a variable"
  return withSpan (← span map j info).info (← variableName j)

private partial def term (map : FileMap) (parent : Span) (pattern : Bool)
    (j : Json) : DecodeM (TSyntax `term) := do
  let info ← span map j parent
  let kind ← str j "kind"
  if pattern && kind ∈ ["local_call", "remote_call", "fun_call", "bind", "return", "raise", "match"] then
    throw s!"{kind} is not valid in patterns"
  let result ← match kind with
  | "wildcard" => do
    fields j ["kind", "span"]
    unless pattern do throw "wildcard is only valid in patterns"
    pure (Unhygienic.run `(_))
  | "var" => do
    fields j ["kind", "name", "span"]
    pure ⟨(← variableName j).raw⟩
  | "integer" => do
    fields j ["kind", "value", "span"]
    let value ← (← field j "value").getInt?
    let literal : TSyntax `term := ⟨← Parser.runParserCategory (← read) `term (toString value)⟩
    let ctor := mkIdent ``Lynx.Term.integer
    pure (Unhygienic.run `($ctor $literal))
  | "atom" => do
    fields j ["kind", "value", "span"]
    let literal : TSyntax `term := ⟨Syntax.mkStrLit (← str j "value")⟩
    let ctor := mkIdent ``Lynx.Term.atom
    pure (Unhygienic.run `($ctor $literal))
  | "nil" => do
    fields j ["kind", "span"]
    pure ⟨(mkIdent ``Lynx.Term.nil).raw⟩
  | "cons" => do
    fields j ["kind", "head", "tail", "span"]
    let head ← term map info pattern (← field j "head")
    let tail ← term map info pattern (← field j "tail")
    let ctor := mkIdent ``Lynx.Term.cons
    pure (Unhygienic.run `($ctor $head $tail))
  | "function" => do
    fields j ["kind", "id", "arity", "captures", "span"]
    let id : TSyntax `term := ⟨Syntax.mkNumLit (toString (← (← field j "id").getNat?))⟩
    let arity : TSyntax `term := ⟨Syntax.mkNumLit (toString (← (← field j "arity").getNat?))⟩
    let captures ← (← arr j "captures").mapM (term map info pattern)
    let ctor := mkIdent ``Lynx.Term.function
    pure (Unhygienic.run `($ctor $id $arity #[$captures,*]))
  | "local_call" | "remote_call" => do
    fields j (if kind == "local_call" then ["kind", "name", "args", "span"]
      else ["kind", "module", "name", "args", "span"])
    let args ← (← arr j "args").mapM (term map info false)
    let name := functionName (← str j "name") args.size
    let fn ← if kind == "local_call" then pure name else do
      let namespaceId ← identifier (← str j "module")
      pure (mkIdent (namespaceId.getId ++ name.getId))
    if args.isEmpty then pure ⟨fn.raw⟩
    else pure (Unhygienic.run `($fn $args*))
  | "fun_call" => do
    fields j ["kind", "function", "args", "span"]
    let fn ← term map info false (← field j "function")
    let args ← (← arr j "args").mapM (term map info false)
    let apply := mkIdent ``Lynx.Term.apply
    pure (Unhygienic.run `($apply $fn #[$args,*]))
  | "bind" => do
    fields j ["kind", "var", "computation", "body", "span"]
    let binder ← field j "var"
    let var : TSyntax `term ← if (← str binder "kind") == "wildcard" then
      term map info true binder
    else pure ⟨(← param map info binder).raw⟩
    let computation ← term map info false (← field j "computation")
    let body ← term map info false (← field j "body")
    let item := withSpan info.info (Unhygienic.run `(doSeqItem| let $var:term ← $computation:term))
    -- Consecutive Core binds share one block; preserve locations on each statement.
    match body with
    | `(do $items:doSeqItem*) => pure (Unhygienic.run `(do $item:doSeqItem $items:doSeqItem*))
    | _ =>
      let last := Unhygienic.run `(doSeqItem| $body:term)
      pure (Unhygienic.run `(do $item:doSeqItem $last:doSeqItem))
  | "return" => do
    fields j ["kind", "value", "span"]
    let value ← term map info false (← field j "value")
    -- `pure` remains local to this computation, including inside a bind's RHS.
    let pureId := mkIdent `pure
    pure (Unhygienic.run `($pureId $value))
  | "raise" => do
    fields j ["kind", "class", "reason", "span"]
    let ctor ← match ← str j "class" with
      | "error" => pure (mkIdent ``Lynx.Exception.error)
      | "throw" => pure (mkIdent ``Lynx.Exception.throw)
      | "exit" => pure (mkIdent ``Lynx.Exception.exit)
      | other => throw s!"unsupported exception class '{other}'"
    let reason ← term map info false (← field j "reason")
    let error := mkIdent ``Lynx.Result.error
    pure (Unhygienic.run `($error ($ctor $reason)))
  | "match" => do
    fields j ["kind", "expressions", "cases", "span"]
    let exprs ← (← arr j "expressions").mapM (term map info false)
    let unit : TSyntax `term := ⟨(mkIdent ``Unit.unit).raw⟩
    let cases ← (← arr j "cases").mapM fun c => do
      fields c ["patterns", "body", "span"]
      let ci ← span map c info
      let pats ← (← arr c "patterns").mapM (term map ci true)
      unless pats.size == exprs.size do throw "match case must have one pattern per expression"
      let pats := if pats.isEmpty then #[unit] else pats
      let body ← term map ci false (← field c "body")
      pure (withSpan ci.info (Unhygienic.run `(Lean.Parser.Term.matchAltExpr| | $pats,* => $body)))
    if cases.isEmpty then throw "match requires at least one case"
    let exprs := if exprs.isEmpty then #[unit] else exprs
    pure (Unhygienic.run `(match $[$exprs:term],* with $cases:matchAlt*))
  | _ => throw s!"unsupported {if pattern then "pattern" else "term"} kind '{kind}'"
  return withSpan info.info result

private def proofPosition (proofMap : FileMap) (start : Position) (indentation : Nat)
    (pos : String.Pos.Raw) : Position :=
  let p := proofMap.toPosition pos
  if p.line < 2 then start
  else ⟨start.line + p.line - 2, p.column + if p.line == 2 then start.column else indentation⟩

/-- Parsed proof nodes retain their individual ranges in the original file map,
including Unicode columns, relative to the supplied proof origin. -/
private partial def locateProof (map proofMap : FileMap) (start : Position)
    (indentation : Nat) (anchor : Span) (stx : Syntax) : DecodeM Syntax := do
  let pos? := stx.getPos?
  let stop? := stx.getTailPos?
  let mut stx := stx
  if let .node info kind args := stx then
    stx := .node info kind (← args.mapM (locateProof map proofMap start indentation anchor))
  let some pos := pos? | return stx
  let stop := stop?.getD pos
  let location := match anchor.location with
    | .unknown => Location.unknown
    | .line _ => .line (proofPosition proofMap start indentation pos).line
    | .column _ => .column (proofPosition proofMap start indentation pos)
  let info := SourceInfo.synthetic
    (map.ofPosition (proofPosition proofMap start indentation pos))
    (map.ofPosition (proofPosition proofMap start indentation stop)) true
  modify fun s => { s with spans := s.spans.push ⟨info, location⟩ }
  return stx.setInfo info

private def leanProof (map : FileMap) (parent : Span) (name : Name) (j : Json) : DecodeM (TSyntax `term × Span) := do
  fields j ["source", "indentation", "span"]
  let info ← span map j parent
  let indentation ← (← field j "indentation").getNat?
  let input := "by\n" ++ (← str j "source")
  let ctx := Parser.mkInputContext input "<proof>" (normalizeLineEndings := false)
  let parser := Parser.andthenFn Parser.whitespace (Parser.categoryParserFnImpl `term)
  let env ← read
  let parsed := parser.run ctx { env, options := {} } (Parser.getTokenTable env) (Parser.mkParserState input)
  let parsed := if parsed.allErrors.isEmpty && !ctx.atEnd parsed.pos then
    parsed.mkError "end of input" else parsed
  let start := match info.location with
    | .column p => p
    | .line line => ⟨line, 0⟩
    | .unknown => ⟨1, 0⟩
  for (pos, _, error) in parsed.allErrors do
    let p := proofPosition ctx.fileMap start indentation pos
    let location := match info.location with
      | .unknown => Location.unknown
      | .line _ => .line p.line
      | .column _ => .column p
    modify fun s => { s with diagnostics := s.diagnostics.push ⟨name, toString error, location⟩ }
  if !parsed.allErrors.isEmpty then return (⟨.missing⟩, info)
  return (⟨← locateProof map ctx.fileMap start indentation info parsed.stxStack.back⟩, info)

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

private partial def command (map : FileMap) (j : Json) (parent : Span := {})
    (wrapPurity : Bool := true) : DecodeM (TSyntax `command) := do
  let info ← span map j parent
  let kind ← str j "kind"
  let result ← match kind with
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
    pure (Unhygienic.run `(def $name : $tableType := $body))
  | "mutual" => do
    fields j ["kind", "defs", "pure", "span"]
    let defs ← arr j "defs"
    if defs.isEmpty then throw "mutual requires at least one definition"
    let decls ← defs.mapM fun decl => do
      unless (← str decl "kind") == "def" do throw "mutual requires def declarations"
      unless (← (← field decl "pure").getBool?) == (← (← field j "pure").getBool?) do
        throw "mutual definitions must agree with the group purity"
      command map decl info false
    pure (Unhygienic.run `(mutual $decls:command* end))
  | "theorem" => do
    fields j ["kind", "name", "params", "requires", "ensures", "proof", "span"]
    let params ← (← arr j "params").mapM fun p => do
      pure (mkIdent (Name.mkSimple (← p.getStr?)))
    let arity := params.size
    let args := params.map fun p => (⟨p.raw⟩ : TSyntax `term)
    let name := functionName (← str j "name") arity
    let termType := mkIdent ``Lynx.Term
    let binders := params.map fun p => Unhygienic.run `(bracketedBinder| ($p : $termType))
    let requirement ← match field j "requires" with
      | .error _ => pure none
      | .ok value => do
        let callee := functionName (← value.getStr?) arity
        pure (some (Unhygienic.run `($callee $args*)))
    let ensuresName := functionName (← str j "ensures") arity
    let ensures := Unhygienic.run `($ensuresName $args*)
    let (proof, proofInfo) ← leanProof map info name.getId (← field j "proof")
    modify fun s => { s with theorems := s.theorems.push (name.getId, proofInfo) }
    let ok := mkIdent ``Lynx.Result.ok
    let trueTerm := mkIdent ``Lynx.Term.true
    let hypothesis := mkIdent `requires
    let binders := match requirement with
      | none => binders
      | some requires =>
        binders.push (Unhygienic.run `(bracketedBinder| ($hypothesis : $requires = $ok $trueTerm)))
    pure (Unhygienic.run `(theorem $name $binders:bracketedBinder*
      : $ensures = $ok $trueTerm := $proof))
  | "def" => do
    fields j ["kind", "name", "params", "body", "pure", "span"]
    let params ← (← arr j "params").mapM (param map info)
    let name := functionName (← str j "name") params.size
    let termType := mkIdent ``Lynx.Term
    let resultType := mkIdent ``Lynx.Result
    let binders := params.map fun p => Unhygienic.run `(bracketedBinder| ($p : $termType))
    let body ← term map info false (← field j "body")
    pure (Unhygienic.run `(def $name $binders:bracketedBinder* : $resultType := $body))
  | _ => throw s!"unsupported command kind '{kind}'"
  let isPure ← if kind ∈ ["def", "mutual"] then (← field j "pure").getBool? else pure false
  -- A mutual group gets one joint purity proof, rather than wrapping its members.
  let result := if wrapPurity && isPure then
    Unhygienic.run `(#lynx_pure $result:command)
    else result
  return withSpan info.info result

/-- Table metadata also gives kernel-checked application equations for both pure
and effectful entries, so proofs can simplify translated `Term.apply` calls
without inspecting the table or duplicating callback implementations. Pure calls
preserve depth; effectful bodies consume one level while their caller's
continuation retains its original depth. -/
private def commands (map : FileMap) (j : Json) : DecodeM (Array (TSyntax `command)) := do
  let errors := (← get).diagnostics.size
  let declaration ← command map j
  if (← get).diagnostics.size != errors then return #[]
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
      pure (Unhygienic.run `(@[simp↓] theorem $name {$alpha:ident : Type} ($depth:ident : $natType)
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
      pure (Unhygienic.run `(@[simp↓] theorem $name {$alpha:ident : Type} ($depth:ident : $natType)
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
      pure (Unhygienic.run `(@[simp↓] theorem $explicitName {$alpha:ident : Type} ($depth:ident : $natType)
        $binders:bracketedBinder* ($next:ident : $termType → $resultType $alpha:ident) :
        $resolve $table $depth:ident ($bind ($apply ($function $id $arity #[$captures,*]) #[$arguments,*]) $next:ident) =
          $resolve $table $depth:ident ($bind $body $next:ident) := by
        exact $name $depth:ident $parameters* $next:ident))
    else
      pure (Unhygienic.run `(@[simp↓] theorem $explicitName {$alpha:ident : Type} ($depth:ident : $natType)
        $binders:bracketedBinder* ($next:ident : $termType → $resultType $alpha:ident) :
        $resolve $table ($depth:ident + 1) ($bind ($apply ($function $id $arity #[$captures,*]) #[$arguments,*]) $next:ident) =
          $bind ($resolve $table $depth:ident $body) (fun $value:ident => $resolve $table ($depth:ident + 1) ($next:ident $value:ident)) := by
        exact $name $depth:ident $parameters* $next:ident))
    result := result.push (withSpan info.info explicitLemma)
    let reduction ← if entry.isPure then
      pure (Unhygienic.run `(@[simp] theorem $callName ($depth:ident : $natType)
        $binders:bracketedBinder* :
        $resolve $table $depth:ident ($apply ($function $id $arity #[$captures,*]) #[$arguments,*]) = $body := by
        simpa only [($bindOk), ($resolvePure $table $depth:ident $body (by simp))] using $name $depth:ident $parameters* (fun $value:ident => $ok $value:ident)))
    else
      pure (Unhygienic.run `(@[simp] theorem $callName ($depth:ident : $natType)
        $binders:bracketedBinder* :
        $resolve $table ($depth:ident + 1) ($apply ($function $id $arity #[$captures,*]) #[$arguments,*]) =
          $resolve $table $depth:ident $body := by
        simpa only [($bindOk), ($resolvePure), ($pureOk)] using $name $depth:ident $parameters* (fun $value:ident => $ok $value:ident)))
    result := result.push (withSpan info.info reduction)
  return result

private def diagnostic (file moduleName severity message : String)
    (location : Location := .unknown) (declarationName : Option Name := none) : Json :=
  Json.mkObj <| [("file", toJson file), ("module", toJson moduleName),
    ("declaration", toJson (declarationName.map Name.getString!)),
    ("severity", toJson severity), ("message", toJson message)] ++
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

/-- Read declaration identifiers from generated syntax, including purity wrappers.
A command containing several declarations has no single declaration name. -/
private partial def declarationNames (stx : Syntax) : Array Name :=
  if stx.isOfKind ``Lean.Parser.Command.declaration then
    let id := stx[1][1]
    let id := if id.isIdent then id else id[0]
    if id.isIdent then #[id.getId] else #[]
  else
    stx.getArgs.foldl (fun names child => names ++ declarationNames child) #[]

private def elaborateFile (env : Lean.Environment) (file : String) (map : FileMap)
    (commands : Array (TSyntax `command))
    : IO (Elab.Command.State × Array (Message × Option Name)) := do
  let action : Elab.Command.CommandElabM (Array (Message × Option Name)) := do
    let mut messages := #[]
    for cmd in commands do
      let names := declarationNames cmd.raw
      let declarationName := if names.size == 1 then names[0]? else none
      Elab.Command.elabCommandTopLevel cmd
      for msg in (← get).messages.toList do
        messages := messages.push (msg, declarationName)
    return messages
  let (messages, state) ← (action.run { fileName := file, fileMap := map, snap? := none, cancelTk? := none }).run
    (Elab.Command.mkState env {} (Options.empty.setBool `Elab.async false)) |>.toIO
      (fun _ => IO.userError "runner elaboration failed")
  return (state, messages)

/-- One input file, decoded directly to Lean commands without elaboration. -/
structure DecodedFile where
  fileName : String
  moduleName : String
  imports : Array String
  fileMap : FileMap
  commands : Array (TSyntax `command)
  private cacheKey : Option String
  private spans : Array Span
  private proofDiagnostics : Array ProofDiagnostic
  private theorems : Array (Name × Span)
  private reexportImports : Bool

/-- Immutable runtime imports, reused without retaining translated declarations. -/
private structure Runtime where
  env : Lean.Environment
  imports : ImportState

private def runtimeImports : Array Import := #[{ module := `Lynx, isExported := true }]

private def getRuntime (cache : IO.Ref (Option Runtime)) : IO Runtime := do
  if let some runtime ← cache.get then return runtime
  unsafe enableInitializersExecution
  let runtime ← withImporting do
    let (_, state) ← (importModulesCore runtimeImports (globalLevel := .exported)).run
    let env ← finalizeImport state runtimeImports {} 0 false true (level := .exported)
    pure ({ env, imports := state } : Runtime)
  cache.set (some runtime)
  return runtime

private def importFile (runtime : Runtime) (imports : Array Import)
    (artifacts : NameMap ImportArtifacts) : IO Lean.Environment := do
  if imports == runtimeImports then return runtime.env
  unsafe enableInitializersExecution
  withImporting do
    -- Each file extends the runtime's import state, never a preceding file's state.
    let (_, state) ← (importModulesCore imports (globalLevel := .exported) (arts := artifacts)).run runtime.imports
    finalizeImport state imports {} 0 false true (level := .exported)

/-- Reserve synthetic offsets for supplied spans and embedded proof locations. -/
private partial def sourceExtent (j : Json) : Nat × Nat := Id.run do
  let mut lines := 1
  let mut columns := 1
  if let .ok xs := arr j "span" then
    if let some line := xs[0]? then
      lines := max lines (line.getNat?.toOption.getD 1)
    if let some column := xs[1]? then
      columns := max columns (column.getNat?.toOption.getD 1)
  if let .ok source := str j "source" then
    lines := lines + (source.splitOn "\n").length + 1
    columns := columns + source.length + (field j "indentation" >>= Json.getNat?).toOption.getD 0
  let children : Array Json := match j with
    | .arr xs => xs
    | .obj xs => xs.toArray.map (·.2)
    | _ => #[]
  for child in children do
    let (l, c) := sourceExtent child
    lines := max lines l
    columns := max columns c
  return (lines, columns)

private def sourceMap (entry : Json) : FileMap :=
  let (lines, columns) := sourceExtent entry
  let line := String.ofList (List.replicate columns ' ')
  FileMap.ofString (String.intercalate "\n" (List.replicate lines line))

/-- Decode input files after the selected command requests them. -/
private def decode (files : Array Json) (env : Lean.Environment) : IO (Array DecodedFile) := do
  files.mapM fun entry => do
    let file ← IO.ofExcept (str entry "file")
    try
      let moduleName ← IO.ofExcept (str entry "module")
      let key ← (entry.getObjVal? "cache_key").toOption.mapM fun value => do
        let key ← IO.ofExcept value.getStr?
        unless key.length == 64 && key.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) do
          throw (IO.userError "cache_key must be a SHA-256 hex digest")
        pure key
      let map := sourceMap entry
      let (moduleName, imports, commands, state, reexportImports) ← IO.ofExcept do
        fields entry ["file", "module", "imports", "contents", "cache_key"]
        let namespaceId ← (identifier moduleName).run env |>.run' {}
        let imports ← (← arr entry "imports").mapM fun j => do
          let name ← j.getStr?
          let name := if name.startsWith "Erlang." &&
              (name == moduleName || !files.any (fun file => (str file "module").toOption == some name)) then
            "Lynx.Modules." ++ name
            else name
          let id ← (identifier name).run env |>.run' {}
          pure id.getId.toString
        let contents ← arr entry "contents"
        let reexportImports := !contents.isEmpty
        let (commands, state) ← contents.mapM (commands map) |>.run env |>.run {}
        let visibility := Unhygienic.run `(@[expose] public section)
        let start := Unhygienic.run `(namespace $namespaceId)
        let stop := Unhygienic.run `(end $namespaceId)
        pure (namespaceId.getId.toString, imports,
          #[visibility, start] ++ commands.flatten ++ #[stop], state, reexportImports)
      return ⟨file, moduleName, imports, map, commands, key,
        state.spans, state.diagnostics, state.theorems, reexportImports⟩
    catch err => throw (IO.userError s!"{file}: {err}")

private def parsingDiagnostics (file : DecodedFile) : Array Json :=
  file.proofDiagnostics.map fun error =>
    diagnostic file.fileName file.moduleName "error"
      error.message error.location (some error.declarationName)

private def renderFile (file : DecodedFile) (env : Lean.Environment) : IO String := do
  let action : CoreM String := do
    let commands ← file.commands.mapM fun cmd => do
      return (← PrettyPrinter.ppCommand cmd).pretty 100
    -- Exposed definitions and public law types mention imported operations.
    let importPrefix := if file.reexportImports then "public import " else "import "
    let imports := file.imports.toList.map (importPrefix ++ ·)
    return "module\n\n" ++ String.intercalate "\n" ("public import Lynx" :: imports) ++
      "\n\n" ++ String.intercalate "\n\n" commands.toList ++ "\n"
  (action.run' { fileName := file.fileName, fileMap := file.fileMap }
    { env := env }).toIO (fun _ => IO.userError s!"{file.fileName}: Lean source rendering failed")

private def cachedArtifacts (directory : System.FilePath) : ImportArtifacts :=
  let path := directory / "module.olean"
  .ofArrays #[#[path, path.withExtension "olean.server", path.withExtension "olean.private"],
    #[path.withExtension "ir.sig", path.withExtension "ir"]]

private def cachedDiagnostics (directory : System.FilePath) : IO (Option (Array Json)) := do
  try
    let metadata ← IO.ofExcept <| Json.parse (← IO.FS.readFile (directory / "result.json"))
    unless (← IO.ofExcept (str metadata "version")) == "1" do return none
    return some (← IO.ofExcept (arr metadata "diagnostics"))
  catch _ => return none

/-- Lake's artifact hashes identify the compiled runner and runtime, including local changes. -/
private def runtimeFingerprint : IO UInt64 := do
  let runner ← findOLean `Lynx.Runner
  let directory := runner.parent.get!
  let root := directory.parent.get!
  -- Include Lynx's root-module hashes beside the Lynx/ directory.
  let rootHashes := (← root.readDir).filter (·.fileName.startsWith "Lynx.")
  let paths := (← directory.walkDir) ++ rootHashes.map (·.path)
  let paths := paths.filter (·.toString.endsWith ".hash")
    |>.qsort (fun a b => a.toString < b.toString)
  let mut result := hash ("lynx-cache-1" : String)
  for path in paths do
    result := mixHash result (hash (path.toString.drop (root.toString.length + 1) |>.toString,
      ← IO.FS.readFile path))
  return result

/-- Publish complete, successfully audited entries atomically on the cache filesystem. -/
private def writeCached (directory : System.FilePath) (env : Lean.Environment)
    (diagnostics : Array Json) : IO Unit := do
  let parent := directory.parent.getD directory
  IO.FS.createDirAll parent
  let temporary := parent / s!".tmp-{hash (← IO.getRandomBytes 16)}"
  IO.FS.createDir temporary
  try
    writeModule env (temporary / "module.olean")
    IO.FS.writeFile (temporary / "result.json")
      (Json.mkObj [("version", toJson ("1" : String)), ("diagnostics", .arr diagnostics)]).compress
    if (← cachedDiagnostics directory).isSome then return
    if ← directory.pathExists then
      if (← cachedDiagnostics directory).isSome then return
      IO.FS.removeDirAll directory
    IO.FS.rename temporary directory
  catch error =>
    -- Another verifier may have published the same entry concurrently.
    unless (← cachedDiagnostics directory).isSome do throw error
  finally
    if ← temporary.pathExists then IO.FS.removeDirAll temporary

/-- Verify against explicit imports, reusing only successfully audited module artifacts. -/
private def verify (files : Array DecodedFile) (runtime : Runtime)
    (cacheDirectory : System.FilePath) (emit : Json → IO Unit) : IO Unit := do
  IO.FS.withTempDir fun temporary => do
    let mut artifacts : NameMap ImportArtifacts := {}
    let mut verified : Std.HashSet String := {}
    let mut uncached : Std.HashSet String := {}
    for file in files do
      let started ← IO.monoMsNow
      let source ← renderFile file runtime.env
      let mut fileFailed := !file.proofDiagnostics.isEmpty
      let mut diagnostics := parsingDiagnostics file
      let mut imports := runtimeImports
      let mut missingImport := false
      let mut cacheHit := false
      for name in file.imports do
        let moduleName ← IO.ofExcept <| (identifier name).run runtime.env |>.run' {}
        let moduleName := moduleName.getId
        if files.any (·.moduleName == name) && !verified.contains name then
          missingImport := true
          diagnostics := diagnostics.push (diagnostic file.fileName file.moduleName "error"
            s!"import '{name}' must precede this file and verify successfully")
        unless imports.any (·.module == moduleName) do
          imports := imports.push { module := moduleName, isExported := file.reexportImports }
      unless missingImport do
        let env ← importFile runtime imports artifacts
        let moduleName ← IO.ofExcept <| (identifier file.moduleName).run runtime.env |>.run' {}
        let mainModule := moduleName.getId
        let key := if file.imports.any uncached.contains then none else file.cacheKey
        let directory := key.map (cacheDirectory / ·) |>.getD (temporary / toString (hash mainModule))
        if let some saved ← if fileFailed || key.isNone then pure none else cachedDiagnostics directory then
          diagnostics := saved
          cacheHit := true
        else
          let (state, messages) ← elaborateFile (env.setMainModule mainModule)
            file.fileName file.fileMap file.commands
          for (msg, declarationName) in messages do
            if msg.severity == .error then fileFailed := true
            diagnostics := diagnostics.push (diagnostic file.fileName file.moduleName
              msg.severity.toString
              (← msg.data.toString) (messageLocation file.fileMap file.spans msg) declarationName)
          -- Audit local laws and the precomputed axiom dependencies of imported declarations.
          unless fileFailed do
            let audit : CoreM (Array Json) := do
              let mut errors := #[]
              let namespaceId ← IO.ofExcept <| (identifier file.moduleName).run (← getEnv) |>.run' {}
              for (name, info) in file.theorems do
                for axiomName in ← collectAxioms (namespaceId.getId ++ name) do
                  unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
                    errors := errors.push (diagnostic file.fileName file.moduleName "error"
                      s!"unexpected axiom: {axiomName}" info.location (some name))
              return errors
            let errors ← (audit.run' { fileName := file.fileName, fileMap := file.fileMap }
              { env := state.env }).toIO (fun _ => IO.userError "law axiom audit failed")
            if !errors.isEmpty then fileFailed := true
            diagnostics := diagnostics ++ errors
          unless fileFailed do
            if key.isSome then
              writeCached directory state.env diagnostics
            else
              IO.FS.createDirAll directory
              writeModule state.env (directory / "module.olean")
        unless fileFailed do
          artifacts := artifacts.insert mainModule (cachedArtifacts directory)
          verified := verified.insert file.moduleName
          if key.isNone then uncached := uncached.insert file.moduleName
      let elapsed := (← IO.monoMsNow) - started
      let status := if missingImport then "skipped" else if fileFailed then "error" else "ok"
      emit (Json.mkObj [
        ("status", toJson status),
        ("file", toJson file.fileName), ("module", toJson file.moduleName),
        ("source", toJson source), ("time_ms", toJson elapsed),
        ("cached", toJson cacheHit), ("diagnostics", .arr diagnostics)])

private def runFiles (j : Json) (cache : IO.Ref (Option Runtime)) (emit : Json → IO Unit) : IO Unit := do
  let files ← IO.ofExcept do
    fields j ["command", "version", "files", "cache_dir"]
    arr j "files"
  let directory := System.FilePath.mk (← IO.ofExcept (str j "cache_dir"))
  unless files.isEmpty do
    let runtime ← getRuntime cache
    let decoded ← decode files runtime.env
    let directory ← if decoded.any (·.cacheKey.isSome) then
      pure (directory / s!"lean-{Lean.versionString}-{← runtimeFingerprint}")
      else pure directory
    verify decoded runtime directory emit

private def run (request : String) (cache : IO.Ref (Option Runtime)) (emit : Json → IO Unit) : IO Unit := do
  try
    let j ← IO.ofExcept (Json.parse request)
    let command ← IO.ofExcept (str j "command")
    let version ← IO.ofExcept (str j "version")
    unless version == "1.0" do throw (IO.userError "unsupported version")
    unless command == "verify" do throw (IO.userError s!"unsupported runner command '{command}'")
    runFiles j cache emit
    emit (Json.mkObj [("status", toJson "done")])
  catch err =>
    emit (Json.mkObj [("status", toJson "failure"), ("message", toJson err.toString)])

end Lynx.Runner

/-- Process newline-delimited JSON requests until stdin closes. -/
public def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    Lean.initSearchPath (← Lean.findSysroot)
    let cache ← IO.mkRef (none : Option Lynx.Runner.Runtime)
    let stdin ← IO.getStdin
    let stdout ← IO.getStdout
    let emit := fun payload : Lean.Json => do
      stdout.putStrLn payload.compress
      stdout.flush
    repeat
      let request ← stdin.getLine
      if request.isEmpty then break
      Lynx.Runner.run request cache emit
    return 0
  | _ =>
    IO.println (Lean.Json.mkObj [("status", Lean.toJson "failure"),
      ("message", Lean.toJson "usage: Runner.lean")]).compress
    return 2
