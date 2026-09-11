import Lean
import Lynx

/-! A deliberate snapshot of Lynx's exported modules and declarations.
Any public API addition or removal must update this file. -/

namespace LynxTest.PublicApi
open Lean Elab Command

private def expectedModules : Array String := #[
  "Lynx",
  "Lynx.Modules.Erlang",
  "Lynx.Modules.Extensions",
  "Lynx.Modules.Maps",
  "Lynx.Term"
]

private def expectedDeclarations : Array String := #[
  "Lynx.Environment",
  "Lynx.Environment.currentPid",
  "Lynx.Environment.currentProcess",
  "Lynx.Environment.mk",
  "Lynx.Environment.pdict",
  "Lynx.Environment.pidCounter",
  "Lynx.Environment.processes",
  "Lynx.Environment.setPdict",
  "Lynx.Exception",
  "Lynx.Exception.error",
  "Lynx.Exception.exit",
  "Lynx.Exception.throw",
  "Lynx.Modules.Erlang.add_2",
  "Lynx.Modules.Erlang.andalso_2",
  "Lynx.Modules.Erlang.append_2",
  "Lynx.Modules.Erlang.equal_2",
  "Lynx.Modules.Erlang.erase_0",
  "Lynx.Modules.Erlang.erase_1",
  "Lynx.Modules.Erlang.get_0",
  "Lynx.Modules.Erlang.get_1",
  "Lynx.Modules.Erlang.get_keys_0",
  "Lynx.Modules.Erlang.get_keys_1",
  "Lynx.Modules.Erlang.greater_than_2",
  "Lynx.Modules.Erlang.greater_than_or_equal_2",
  "Lynx.Modules.Erlang.is_integer_1",
  "Lynx.Modules.Erlang.is_list_1",
  "Lynx.Modules.Erlang.less_than_2",
  "Lynx.Modules.Erlang.less_than_or_equal_2",
  "Lynx.Modules.Erlang.put_2",
  "Lynx.Modules.Erlang.self_0",
  "Lynx.Modules.Extensions.is_map_2",
  "Lynx.Modules.Extensions.is_proper_list_1",
  "Lynx.Modules.Extensions.is_proper_list_2",
  "Lynx.Modules.Maps.get_2",
  "Lynx.Modules.Maps.merge_2",
  "Lynx.Modules.Maps.new_0",
  "Lynx.Modules.Maps.put_3",
  "Lynx.PID",
  "Lynx.ProcessState",
  "Lynx.ProcessState.mk",
  "Lynx.ProcessState.pdict",
  "Lynx.Result",
  "Lynx.Result.IsPure",
  "Lynx.Result.error",
  "Lynx.Result.ok",
  "Lynx.Term",
  "Lynx.Term.Equivalent",
  "Lynx.Term.atom",
  "Lynx.Term.compare",
  "Lynx.Term.cons",
  "Lynx.Term.emptyMap",
  "Lynx.Term.false",
  "Lynx.Term.instDecidableEquivalent",
  "Lynx.Term.integer",
  "Lynx.Term.isFalse",
  "Lynx.Term.isTrue",
  "Lynx.Term.le",
  "Lynx.Term.map",
  "Lynx.Term.nil",
  "Lynx.Term.pid",
  "Lynx.Term.true",
  "Lynx.Term.tuple",
  "Lynx.instBEqTerm",
  "Lynx.instInhabitedEnvironment",
  "Lynx.instInhabitedProcessState",
  "Lynx.instReprEnvironment",
  "Lynx.instReprException",
  "Lynx.instReprProcessState",
  "Lynx.instReprTerm",
  "Lynx.run",
]

private def sorted (items : List String) : Array String :=
  (items.mergeSort (fun left right => left < right)).toArray

private def privateModules : Array String := #[
  "Lynx.Attribute",
  "Lynx.Modules.Erlang.Definitions",
  "Lynx.Modules.Erlang.ListLemmas",
  "Lynx.Tactic",
  "Lynx.Tactic.Contract",
  "Lynx.Term.Compare",
  "Lynx.Term.DataTypes",
  "Lynx.Term.Induction",
  "Lynx.Term.Map"
]

private def apiContributorModules : Array String := #[
  "Lynx",
  "Lynx.Modules.Erlang",
  "Lynx.Modules.Erlang.Definitions",
  "Lynx.Modules.Extensions",
  "Lynx.Modules.Maps",
  "Lynx.Term",
  "Lynx.Term.Compare",
  "Lynx.Term.DataTypes"
]

private def actualModules (env : Environment) : Array String :=
  sorted <| env.header.moduleNames.toList.filterMap fun name =>
    let name := name.toString
    if (name == "Lynx" || name.startsWith "Lynx.") && !privateModules.contains name then
      some name
    else none

private def actualDeclarations : CoreM (Array String) := do
  let env ← getEnv
  let declarations ← env.constants.toList.filterMapM fun (name, info) => do
    match env.getModuleIdxFor? name with
    | none => pure none
    | some moduleIdx =>
        let moduleName := env.header.moduleNames[moduleIdx.toNat]!
        let isGenerated := (← Lean.isAutoDeclOrPrivate_Internal name) ||
          Lean.isRecCore env name || Lean.Meta.isInstanceCore env name.getPrefix
        if apiContributorModules.contains moduleName.toString &&
            !info.isTheorem && !isPrivateName name && !isGenerated then
          pure (some name.toString)
        else pure none
  return sorted declarations

private def lines (items : Array String) : String :=
  String.intercalate "\n" items.toList

run_cmd do
  let env ← getEnv
  let modules := actualModules env
  unless modules == expectedModules do
    throwError "public module snapshot changed:\n{lines modules}"
  let declarations ← liftCoreM actualDeclarations
  unless declarations == expectedDeclarations do
    throwError "public declaration snapshot changed:\n{lines declarations}"

end LynxTest.PublicApi
