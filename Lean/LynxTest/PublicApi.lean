module

meta import Lean
public import Lynx.Frontend
public import Lynx

meta section

/-! Snapshot of public types and executable declarations available through `Lynx`
and the frontend command.
Inspect the exporting environment across every Lynx module, so internal helpers
cannot escape the check by living in a module omitted from a contributor list.
Proofs, generated declarations, and meta elaborator code are not snapshotted. -/

namespace LynxTest.PublicApi
open Lean Elab Command

private def expectedDeclarations : Array String := #[
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
  "Lynx.Modules.Erlang.add_2",
  "Lynx.Modules.Erlang.andalso_2",
  "Lynx.Modules.Erlang.append_2",
  "Lynx.Modules.Erlang.apply_2",
  "Lynx.Modules.Erlang.bit_size_1",
  "Lynx.Modules.Erlang.byte_size_1",
  "Lynx.Modules.Erlang.equal_2",
  "Lynx.Modules.Erlang.erase_0",
  "Lynx.Modules.Erlang.erase_1",
  "Lynx.Modules.Erlang.exact_equal_2",
  "Lynx.Modules.Erlang.exact_not_equal_2",
  "Lynx.Modules.Erlang.get_0",
  "Lynx.Modules.Erlang.get_1",
  "Lynx.Modules.Erlang.get_keys_0",
  "Lynx.Modules.Erlang.get_keys_1",
  "Lynx.Modules.Erlang.greater_than_2",
  "Lynx.Modules.Erlang.greater_than_or_equal_2",
  "Lynx.Modules.Erlang.is_binary_1",
  "Lynx.Modules.Erlang.is_bitstring_1",
  "Lynx.Modules.Erlang.is_float_1",
  "Lynx.Modules.Erlang.is_integer_1",
  "Lynx.Modules.Erlang.is_list_1",
  "Lynx.Modules.Erlang.less_than_2",
  "Lynx.Modules.Erlang.less_than_or_equal_2",
  "Lynx.Modules.Erlang.not_equal_2",
  "Lynx.Modules.Erlang.put_2",
  "Lynx.Modules.Erlang.self_0",
  "Lynx.Modules.Erlang.send_2",
  "Lynx.Modules.Erlang.spawn_1",
  "Lynx.Modules.Maps.get_2",
  "Lynx.Modules.Maps.merge_2",
  "Lynx.Modules.Maps.new_0",
  "Lynx.Modules.Maps.put_3",
  "Lynx.Outcome",
  "Lynx.Outcome.deadlock",
  "Lynx.Outcome.error",
  "Lynx.Outcome.ok",
  "Lynx.PID",
  "Lynx.ProcessState",
  "Lynx.ProcessState.mailbox",
  "Lynx.ProcessState.mk",
  "Lynx.ProcessState.pdict",
  "Lynx.Property",
  "Lynx.Result",
  "Lynx.Result.IsPure",
  "Lynx.Result.bind",
  "Lynx.Result.error",
  "Lynx.Result.get",
  "Lynx.Result.handle",
  "Lynx.Result.instMonad",
  "Lynx.Result.instMonadExceptOfException",
  "Lynx.Result.instMonadStateOfEnvironment",
  "Lynx.Result.ok",
  "Lynx.Result.receive",
  "Lynx.Result.run",
  "Lynx.Result.send",
  "Lynx.Result.set",
  "Lynx.Result.spawn",
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
  "Lynx.Term.FiniteFloat.exponent",
  "Lynx.Term.FiniteFloat.fraction",
  "Lynx.Term.FiniteFloat.magnitude",
  "Lynx.Term.FiniteFloat.mk",
  "Lynx.Term.FiniteFloat.negative",
  "Lynx.Term.FiniteFloat.toRat",
  "Lynx.Term.Fun",
  "Lynx.Term.FunTable",
  "Lynx.Term.Map.Entries",
  "Lynx.Term.Map.find",
  "Lynx.Term.Map.merge",
  "Lynx.Term.Map.put",
  "Lynx.Term.atom",
  "Lynx.Term.bitstring",
  "Lynx.Term.compare",
  "Lynx.Term.cons",
  "Lynx.Term.emptyMap",
  "Lynx.Term.exactCompare",
  "Lynx.Term.false",
  "Lynx.Term.fetchFun",
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
  "main",
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
        if (moduleName == "Lynx" || moduleName.startsWith "Lynx.") &&
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
