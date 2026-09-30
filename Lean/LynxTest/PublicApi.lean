module

meta import Lean
public import Lynx.Runner
public import Lynx
public import Erlang.erlang
public import Erlang.lists
public import Erlang.maps

-- Keep the closure environment and table adapter signatures part of the API check.
example : Nat → Nat → Array Lynx.Term → Lynx.Term := Lynx.Term.function
example (entry : Array Lynx.Term → Array Lynx.Term → Lynx.Result) :
    Lynx.Term.FunTable := #[.effectful entry]
example (entry : Array Lynx.Term → Array Lynx.Term → Except Lynx.Exception Lynx.Term) :
    Lynx.Term.FunTable := #[.pure entry]
example : Lynx.Term.FunTable → Lynx.Term → Array Lynx.Term → Lynx.Result :=
  Lynx.Term.pureApply

example : Lynx.Result → Lynx.Term.FunTable → Nat → Lynx.Environment → Lynx.Outcome Lynx.Term :=
  Lynx.Result.runWith
example : Lynx.Term → Lynx.Term → Lynx.Result := Erlang.erlang.«apply/2»
example : Lynx.Term → Array Lynx.Term → Lynx.Result := Lynx.Term.apply
example : Lynx.Term → Lynx.Result := Erlang.erlang.«spawn/1»
example : Lynx.Term → (Except Lynx.Exception Lynx.Term → Lynx.Result α) → Lynx.Result α :=
  Lynx.Result.spawn

meta section

/-! Snapshot of public types and executable declarations available through `Lynx`,
the Erlang runtime modules, and the runner command.
Inspect the exporting environment across every Lynx and Erlang module, so internal helpers
cannot escape the check by living in a module omitted from a contributor list.
Proofs, generated declarations, and meta elaborator code are not snapshotted. -/

namespace LynxTest.PublicApi
open Lean Elab Command

private def expectedDeclarations : Array String := #[
  "Erlang.erlang.«++/2»",
  "Erlang.erlang.«+/2»",
  "Erlang.erlang.«/=/2»",
  "Erlang.erlang.«</2»",
  "Erlang.erlang.«=/=/2»",
  "Erlang.erlang.«=:=/2»",
  "Erlang.erlang.«=</2»",
  "Erlang.erlang.«==/2»",
  "Erlang.erlang.«>/2»",
  "Erlang.erlang.«>=/2»",
  "Erlang.erlang.«apply/2»",
  "Erlang.erlang.«bit_size/1»",
  "Erlang.erlang.«byte_size/1»",
  "Erlang.erlang.«erase/0»",
  "Erlang.erlang.«erase/1»",
  "Erlang.erlang.«get/0»",
  "Erlang.erlang.«get/1»",
  "Erlang.erlang.«get_keys/0»",
  "Erlang.erlang.«get_keys/1»",
  "Erlang.erlang.«is_binary/1»",
  "Erlang.erlang.«is_bitstring/1»",
  "Erlang.erlang.«is_float/1»",
  "Erlang.erlang.«is_integer/1»",
  "Erlang.erlang.«is_list/1»",
  "Erlang.erlang.«put/2»",
  "Erlang.erlang.«self/0»",
  "Erlang.erlang.«send/2»",
  "Erlang.erlang.«spawn/1»",
  "Erlang.lists.«reverse/2»",
  "Erlang.maps.«get/2»",
  "Erlang.maps.«merge/2»",
  "Erlang.maps.«new/0»",
  "Erlang.maps.«put/3»",
  "Lynx.Accepted",
  "Lynx.Covered",
  "Lynx.EnsuresClauses",
  "Lynx.Environment",
  "Lynx.Environment.currentPid",
  "Lynx.Environment.currentProcess",
  "Lynx.Environment.mk",
  "Lynx.Environment.pdict",
  "Lynx.Environment.pidCounter",
  "Lynx.Environment.processes",
  "Lynx.Environment.schedule",
  "Lynx.Environment.setPdict",
  "Lynx.Exception",
  "Lynx.Exception.error",
  "Lynx.Exception.exit",
  "Lynx.Exception.throw",
  "Lynx.Outcome",
  "Lynx.Outcome.deadlock",
  "Lynx.Outcome.error",
  "Lynx.Outcome.exhausted",
  "Lynx.Outcome.ok",
  "Lynx.PID",
  "Lynx.ProcessState",
  "Lynx.ProcessState.mailbox",
  "Lynx.ProcessState.mk",
  "Lynx.ProcessState.pdict",
  "Lynx.Property",
  "Lynx.Result",
  "Lynx.Result.IsPure",
  "Lynx.Result.apply",
  "Lynx.Result.bind",
  "Lynx.Result.error",
  "Lynx.Result.exhausted",
  "Lynx.Result.get",
  "Lynx.Result.handle",
  "Lynx.Result.instMonad",
  "Lynx.Result.instMonadExceptOfException",
  "Lynx.Result.instMonadStateOfEnvironment",
  "Lynx.Result.ofExcept",
  "Lynx.Result.ok",
  "Lynx.Result.receive",
  "Lynx.Result.resolve",
  "Lynx.Result.run",
  "Lynx.Result.runWith",
  "Lynx.Result.schedule",
  "Lynx.Result.send",
  "Lynx.Result.set",
  "Lynx.Result.spawn",
  "Lynx.Result.toExcept",
  "Lynx.Satisfies",
  "Lynx.ScheduleChoice",
  "Lynx.ScheduleChoice.current",
  "Lynx.ScheduleChoice.swap",
  "Lynx.SourceLabel",
  "Lynx.SourceLabel.file",
  "Lynx.SourceLabel.line",
  "Lynx.SourceLabel.mk",
  "Lynx.Term",
  "Lynx.Term.Bitstring.bitSize",
  "Lynx.Term.Bitstring.toBits",
  "Lynx.Term.FiniteFloat",
  "Lynx.Term.FiniteFloat.add",
  "Lynx.Term.FiniteFloat.exponent",
  "Lynx.Term.FiniteFloat.fraction",
  "Lynx.Term.FiniteFloat.magnitude",
  "Lynx.Term.FiniteFloat.mk",
  "Lynx.Term.FiniteFloat.negative",
  "Lynx.Term.FiniteFloat.ofInt",
  "Lynx.Term.FiniteFloat.toRat",
  "Lynx.Term.Fun",
  "Lynx.Term.FunEntry",
  "Lynx.Term.FunEntry.effectful",
  "Lynx.Term.FunEntry.pure",
  "Lynx.Term.FunTable",
  "Lynx.Term.FunTable.entry",
  "Lynx.Term.Map.Entries",
  "Lynx.Term.Map.find",
  "Lynx.Term.Map.merge",
  "Lynx.Term.Map.put",
  "Lynx.Term.PureFun",
  "Lynx.Term.apply",
  "Lynx.Term.atom",
  "Lynx.Term.bitstring",
  "Lynx.Term.compare",
  "Lynx.Term.cons",
  "Lynx.Term.emptyMap",
  "Lynx.Term.exactCompare",
  "Lynx.Term.false",
  "Lynx.Term.float",
  "Lynx.Term.function",
  "Lynx.Term.instDecidableEqFiniteFloat",
  "Lynx.Term.instReprFiniteFloat",
  "Lynx.Term.integer",
  "Lynx.Term.isFalse",
  "Lynx.Term.isMap",
  "Lynx.Term.isTrue",
  "Lynx.Term.le",
  "Lynx.Term.map",
  "Lynx.Term.nil",
  "Lynx.Term.pid",
  "Lynx.Term.pureApply",
  "Lynx.Term.true",
  "Lynx.Term.tuple",
  "Lynx.WithSourceLabel",
  "Lynx.instBEqTerm",
  "Lynx.instCoeFunResultForallEnvironmentOutcome",
  "Lynx.instDecidableEqSourceLabel",
  "Lynx.instInhabitedEnvironment",
  "Lynx.instInhabitedProcessState",
  "Lynx.instInhabitedScheduleChoice",
  "Lynx.instReprEnvironment",
  "Lynx.instReprException",
  "Lynx.instReprOutcome",
  "Lynx.instReprProcessState",
  "Lynx.instReprScheduleChoice",
  "Lynx.instReprSourceLabel",
  "Lynx.instReprTerm",
  "Lynx.instToStringSourceLabel",
  "Lynx.run",
  "main"
]

private def sorted (items : List String) : Array String :=
  (items.mergeSort (fun left right => left < right)).toArray

private def actualDeclarations : MetaM (Array String) := do
  let env := (← getEnv).setExporting true
  let declarations ← env.constants.toList.filterMapM fun (name, info) => do
    match env.getModuleIdxFor? name with
    | none => pure none
    | some moduleIdx =>
        let moduleName := env.header.moduleNames[moduleIdx.toNat]!.toString
        let isGenerated := (← Lean.isAutoDeclOrPrivate_Internal name) ||
          Lean.isRecCore env name || Lean.Meta.isInstanceCore env name.getPrefix
        if (moduleName == "Lynx" || moduleName.startsWith "Lynx." || moduleName.startsWith "Erlang.") &&
            (env.find? name).isSome && !isMarkedMeta env name &&
            !isPrivateName name && !isGenerated then
          if ← Meta.isProp info.type then pure none else pure (some name.toString)
        else pure none
  return sorted declarations

private def lines (items : Array String) : String :=
  String.intercalate "\n" items.toList

run_cmd do
  let declarations ← liftTermElabM actualDeclarations
  unless declarations == expectedDeclarations do
    let added := declarations.filter (!expectedDeclarations.contains ·)
    let removed := expectedDeclarations.filter (!declarations.contains ·)
    throwError "public declaration snapshot changed:\nUnexpected:\n{lines added}\nMissing:\n{lines removed}"

end LynxTest.PublicApi
