module

meta import Lean
public import Lynx.Runner
public import Lynx
public import Lynx.Modules.Erlang.erlang
public import Lynx.Modules.Erlang.lists
public import Lynx.Modules.Erlang.maps
public import Lynx.Modules.Erlang.math

-- Keep constructor and table adapter signatures part of the API check.
private def bitstringConstructor : (bytes : ByteArray) → (lastBits : Fin 8) →
    Lynx.Term.Bitstring.Valid bytes lastBits → Lynx.Term :=
  fun bytes lastBits valid => Lynx.Term.bitstring bytes lastBits valid
private def referenceConstructor : Nat → Lynx.Term := Lynx.Term.reference
private def makeRef : Lynx.Result := Erlang.erlang.«make_ref/0»

-- Bit-field proof interfaces are available through ordinary public imports.
private theorem decodeBigEndian (value width : Nat) :
    Lynx.Term.Bitstring.decodeInteger (Lynx.Term.Bitstring.integerBits value width false) false =
      value % 2 ^ width :=
  Lynx.Term.Bitstring.decodeInteger_integerBits value width

private theorem bitViewRoundTrip (bits : List Bool) :
    Lynx.Term.Bitstring.integerBits (Lynx.Term.Bitstring.decodeInteger bits false)
      bits.length false = bits :=
  Lynx.Term.Bitstring.integerBits_decodeInteger bits

private theorem alignedBitView (bytes : ByteArray) :
    Lynx.Term.Bitstring.ofBits (Lynx.Term.Bitstring.toBits bytes 0) =
      .bitstring bytes 0 (Lynx.Term.Bitstring.valid_aligned bytes) :=
  Lynx.Term.Bitstring.ofBits_toBits_aligned bytes

private theorem utf8ConstructionRoundTrip (value : Nat) (tail : List Bool)
    (bounded : value ≤ 0x10ffff) (scalar : value < 0xd800 ∨ 0xdfff < value) :
    ∃ encoded : List Bool,
      Lynx.Term.Bitstring.utf8Segment (.integer value) =
        .ok (Lynx.Term.Bitstring.ofBits encoded) ∧
      encoded.length % 8 = 0 ∧
      Lynx.Term.Bitstring.matchUtf8 (Lynx.Term.Bitstring.ofBits (encoded ++ tail)) =
        some (.integer value, Lynx.Term.Bitstring.ofBits tail) :=
  Lynx.Term.Bitstring.matchUtf8_construct value tail bounded scalar

private theorem atomEquality (term : Lynx.Term) (name : String) :
    term.exactCompare (.atom name) = .eq ↔ term = .atom name :=
  Lynx.Term.exactCompare_eq_atom term name

private theorem integerEquality (term : Lynx.Term) (value : Int) :
    term.exactCompare (.integer value) = .eq ↔ term = .integer value :=
  Lynx.Term.exactCompare_eq_integer term value

private theorem extractBigEndian (value fieldWidth tailWidth : Nat) :
    Lynx.Term.Bitstring.matchInteger
      (Lynx.Term.Bitstring.ofBits (Lynx.Term.Bitstring.integerBits value (fieldWidth + tailWidth) false))
      (.integer fieldWidth) 1 false false =
        some (.integer (((value >>> tailWidth) % 2 ^ fieldWidth : Nat) : Int),
          Lynx.Term.Bitstring.ofBits (Lynx.Term.Bitstring.integerBits value tailWidth false)) :=
  Lynx.Term.Bitstring.matchInteger_big value fieldWidth tailWidth

private theorem binary64Encoding (value : Lynx.Term.FiniteFloat) :
    ∃ encoded : Nat,
      Lynx.Term.Bitstring.floatSegment (.float value) 64 false =
        .ok (Lynx.Term.Bitstring.ofBits (Lynx.Term.Bitstring.integerBits encoded 64 false)) := by
  obtain ⟨encoded, built, _⟩ := Lynx.Term.Bitstring.floatSegment_fields value
  exact ⟨encoded, built⟩

-- Numeric float ordering is available without unfolding comparison internals.
private theorem floatOrdering (left right : Lynx.Term.FiniteFloat) :
    Lynx.Term.compare (.float left) (.float right) =
      compareOfLessAndEq left.toRat right.toRat :=
  Lynx.Term.compare_floats left right

private theorem floatZeroEncoding (value : Lynx.Term.FiniteFloat) :
    value.toRat = 0 ↔ value.exponent.val = 0 ∧ value.fraction.val = 0 :=
  Lynx.Term.FiniteFloat.toRat_eq_zero value

-- Allocation equations remain usable through ordinary public imports.
private theorem makeRefEquation (env : Lynx.Environment) :
    makeRef env = (.ok (.reference (env.refCounter + 1)),
      { env with refCounter := env.refCounter + 1 }) := by
  simp [makeRef]

private theorem makeRefContinuationEquation (next : Lynx.Term → Lynx.Result α)
    (env : Lynx.Environment) :
    (makeRef >>= next) env = next (.reference (env.refCounter + 1))
      { env with refCounter := env.refCounter + 1 } := by
  simp [makeRef]
example : Nat → Nat → Array Lynx.Term → Lynx.Term := Lynx.Term.function
example (entry : Array Lynx.Term → Array Lynx.Term → Lynx.Result) :
    Lynx.Term.FunTable := #[.effectful entry]
example (entry : Array Lynx.Term → Array Lynx.Term → Except Lynx.Exception Lynx.Term) :
    Lynx.Term.FunTable := #[.pure entry]

example : Lynx.Result → Lynx.Term.FunTable → Nat → Lynx.Environment →
    Lynx.Outcome Lynx.Term × Lynx.Environment :=
  Lynx.Result.runWith
example : Lynx.Result → List Lynx.ScheduleChoice → Lynx.Term.FunTable → Nat →
    Lynx.Outcome Lynx.Term :=
  fun computation schedule table callDepth => Lynx.run computation schedule table callDepth
example : Lynx.Term → Lynx.Term → Lynx.Result := Erlang.erlang.«apply/2»
example : Lynx.Term → Array Lynx.Term → Lynx.Result := Lynx.Term.apply
example : Lynx.Term → Lynx.Result := Erlang.erlang.«spawn/1»
example : Lynx.Term → (Lynx.Environment → Lynx.Term → Option β) →
    (Option β → Lynx.Result α) → Lynx.Result α :=
  Lynx.Result.receiveWith
example : Lynx.PID → Lynx.ScheduleChoice := Lynx.ScheduleChoice.timeout

example : Lynx.Term → (Except Lynx.Exception Lynx.Term → Lynx.Result α) → Lynx.Result α :=
  Lynx.Result.spawn

example : List Lynx.Term → Lynx.Term → List Lynx.Term := Lynx.Term.getMapKeys

example (a b : Int) :
    Erlang.erlang.«=:=/2» (.integer a) (.integer b) = .ok Lynx.Term.true ↔ a = b := by
  simp [Erlang.erlang.«=:=/2», Lynx.Term.true, Lynx.Term.false]

example (a b : String) :
    Erlang.erlang.«=:=/2» (.atom a) (.atom b) = .ok Lynx.Term.true ↔ a = b := by
  simp [Erlang.erlang.«=:=/2», Lynx.Term.true, Lynx.Term.false]

example (keys : List Lynx.Term) (input : Lynx.Term)
    (nonempty : Lynx.Term.getMapKeys keys input ≠ []) :
    (Lynx.Term.getMapKeys keys input).length = keys.length :=
  Lynx.Term.getMapKeys_arity keys input nonempty

-- Conversion cancellation works through ordinary public imports without unfolding.
example (computation : Lynx.Result α) (pure : Lynx.Result.IsPure computation) :
    Lynx.Result.ofExcept (Lynx.Result.toExcept computation pure) = computation := by
  simp

example (table : Lynx.Term.FunTable) (depth : Nat) (computation : Lynx.Result α)
    (pure : Lynx.Result.IsPure computation) :
    Lynx.Result.resolve table depth computation = computation := by
  simp [pure]

example (table : Lynx.Term.FunTable) (depth id arity : Nat)
    (captures arguments : Array Lynx.Term) (body : Array Lynx.Term → Lynx.Term.PureFun)
    (next : Lynx.Term → Lynx.Result α)
    (entry : table[id]? = some (.pure body)) (size : arguments.size = arity) :
    Lynx.Result.resolve table depth (Lynx.Term.apply (.function id arity captures) arguments >>= next) =
      Lynx.Result.resolve table depth (Lynx.Result.ofExcept (body captures arguments) >>= next) :=
  Lynx.Result.resolve_apply_pure table depth id arity captures arguments body next entry size

example (table : Lynx.Term.FunTable) (depth : Nat) (computation : Lynx.Result α)
    (next : α → Lynx.Result β) :
    Lynx.Result.resolve table depth (computation >>= next) =
      (Lynx.Result.resolve table depth computation >>= fun value =>
        Lynx.Result.resolve table depth (next value)) :=
  Lynx.Result.resolve_bind table depth computation next

example (table : Lynx.Term.FunTable) (depth id arity : Nat)
    (captures arguments : Array Lynx.Term) (body : Array Lynx.Term → Lynx.Term.Fun)
    (entry : table[id]? = some (.effectful body)) (size : arguments.size = arity) :
    Lynx.Result.resolve table (depth + 1) (Lynx.Term.apply (.function id arity captures) arguments) =
      Lynx.Result.resolve table depth (body captures arguments) :=
  Lynx.Result.resolve_apply_effectful table depth id arity captures arguments body entry size

example (computation : Lynx.Result α) :
    (do let value ← computation; pure value) = computation := by
  simp

-- Ordinary guard evaluation supports environment reads without process effects.
example (env : Lynx.Environment) :
    Lynx.Result.toExceptRead Erlang.erlang.«self/0» env Erlang.erlang.self_readOnly =
      .ok (.pid env.currentPid) := by rfl

example (computation : Lynx.Result α) (next : α → Lynx.Result β)
    (handler : Lynx.Exception → Lynx.Result β) (pure : Lynx.Result.IsPure computation)
    (nextPure : ∀ value, Lynx.Result.IsPure (next value))
    (handlerPure : ∀ exception, Lynx.Result.IsPure (handler exception)) :
    Lynx.Result.IsPure (Lynx.Result.tryWith computation next handler) := by simp [*]

meta section

/-! Snapshot of public types and executable declarations available through `Lynx`,
the Erlang runtime modules, and the runner command.
Inspect the exporting environment across every Lynx and Erlang module, so internal helpers
cannot escape the check by living in a module omitted from a contributor list.
Proofs, generated declarations, and meta elaborator code are not snapshotted. -/

namespace LynxTest.PublicApi
open Lean Elab Command

private def expectedDeclarations : Array String := #[
  "Erlang.erlang.«*/2»",
  "Erlang.erlang.«++/2»",
  "Erlang.erlang.«+/1»",
  "Erlang.erlang.«+/2»",
  "Erlang.erlang.«-/1»",
  "Erlang.erlang.«-/2»",
  "Erlang.erlang.«//2»",
  "Erlang.erlang.«/=/2»",
  "Erlang.erlang.«</2»",
  "Erlang.erlang.«=/=/2»",
  "Erlang.erlang.«=:=/2»",
  "Erlang.erlang.«=</2»",
  "Erlang.erlang.«==/2»",
  "Erlang.erlang.«>/2»",
  "Erlang.erlang.«>=/2»",
  "Erlang.erlang.«abs/1»",
  "Erlang.erlang.«and/2»",
  "Erlang.erlang.«apply/2»",
  "Erlang.erlang.«atom_to_binary/1»",
  "Erlang.erlang.«atom_to_binary/2»",
  "Erlang.erlang.«band/2»",
  "Erlang.erlang.«binary_part/2»",
  "Erlang.erlang.«binary_part/3»",
  "Erlang.erlang.«binary_to_float/1»",
  "Erlang.erlang.«binary_to_integer/1»",
  "Erlang.erlang.«bit_size/1»",
  "Erlang.erlang.«bnot/1»",
  "Erlang.erlang.«bor/2»",
  "Erlang.erlang.«bsl/2»",
  "Erlang.erlang.«bsr/2»",
  "Erlang.erlang.«bxor/2»",
  "Erlang.erlang.«byte_size/1»",
  "Erlang.erlang.«ceil/1»",
  "Erlang.erlang.«div/2»",
  "Erlang.erlang.«element/2»",
  "Erlang.erlang.«erase/0»",
  "Erlang.erlang.«erase/1»",
  "Erlang.erlang.«error/2»",
  "Erlang.erlang.«error/3»",
  "Erlang.erlang.«exit/1»",
  "Erlang.erlang.«float/1»",
  "Erlang.erlang.«float_to_binary/2»",
  "Erlang.erlang.«floor/1»",
  "Erlang.erlang.«get/0»",
  "Erlang.erlang.«get/1»",
  "Erlang.erlang.«get_keys/0»",
  "Erlang.erlang.«get_keys/1»",
  "Erlang.erlang.«hd/1»",
  "Erlang.erlang.«integer_to_binary/1»",
  "Erlang.erlang.«iolist_to_binary/1»",
  "Erlang.erlang.«is_atom/1»",
  "Erlang.erlang.«is_binary/1»",
  "Erlang.erlang.«is_bitstring/1»",
  "Erlang.erlang.«is_boolean/1»",
  "Erlang.erlang.«is_float/1»",
  "Erlang.erlang.«is_function/1»",
  "Erlang.erlang.«is_function/2»",
  "Erlang.erlang.«is_integer/1»",
  "Erlang.erlang.«is_integer/3»",
  "Erlang.erlang.«is_list/1»",
  "Erlang.erlang.«is_map/1»",
  "Erlang.erlang.«is_map_key/2»",
  "Erlang.erlang.«is_number/1»",
  "Erlang.erlang.«is_pid/1»",
  "Erlang.erlang.«is_port/1»",
  "Erlang.erlang.«is_reference/1»",
  "Erlang.erlang.«is_tuple/1»",
  "Erlang.erlang.«length/1»",
  "Erlang.erlang.«make_ref/0»",
  "Erlang.erlang.«make_tuple/2»",
  "Erlang.erlang.«map_get/2»",
  "Erlang.erlang.«map_size/1»",
  "Erlang.erlang.«max/2»",
  "Erlang.erlang.«min/2»",
  "Erlang.erlang.«node/0»",
  "Erlang.erlang.«node/1»",
  "Erlang.erlang.«not/1»",
  "Erlang.erlang.«or/2»",
  "Erlang.erlang.«put/2»",
  "Erlang.erlang.«rem/2»",
  "Erlang.erlang.«round/1»",
  "Erlang.erlang.«self/0»",
  "Erlang.erlang.«send/2»",
  "Erlang.erlang.«setelement/3»",
  "Erlang.erlang.«size/1»",
  "Erlang.erlang.«spawn/1»",
  "Erlang.erlang.«throw/1»",
  "Erlang.erlang.«tl/1»",
  "Erlang.erlang.«trunc/1»",
  "Erlang.erlang.«tuple_size/1»",
  "Erlang.erlang.«xor/2»",
  "Erlang.lists.«member/2»",
  "Erlang.lists.«reverse/2»",
  "Erlang.maps.«get/2»",
  "Erlang.maps.«merge/2»",
  "Erlang.maps.«new/0»",
  "Erlang.maps.«put/3»",
  "Erlang.maps.«update/3»",
  "Erlang.math.«ceil/1»",
  "Erlang.math.«floor/1»",
  "Lynx.Environment",
  "Lynx.Environment.currentPid",
  "Lynx.Environment.currentProcess",
  "Lynx.Environment.mk",
  "Lynx.Environment.pdict",
  "Lynx.Environment.pidCounter",
  "Lynx.Environment.processes",
  "Lynx.Environment.refCounter",
  "Lynx.Environment.schedule",
  "Lynx.Environment.setPdict",
  "Lynx.Exception",
  "Lynx.Exception.classTerm",
  "Lynx.Exception.error",
  "Lynx.Exception.exit",
  "Lynx.Exception.reason",
  "Lynx.Exception.stacktrace",
  "Lynx.Exception.throw",
  "Lynx.Exception.withReason",
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
  "Lynx.ReceiveTimeout",
  "Lynx.ReceiveTimeout.finite",
  "Lynx.ReceiveTimeout.immediate",
  "Lynx.ReceiveTimeout.infinity",
  "Lynx.ReceiveTimeout.ofTerm",
  "Lynx.Result",
  "Lynx.Result.IsPure",
  "Lynx.Result.IsReadOnly",
  "Lynx.Result.apply",
  "Lynx.Result.bind",
  "Lynx.Result.bindPure",
  "Lynx.Result.error",
  "Lynx.Result.exhausted",
  "Lynx.Result.get",
  "Lynx.Result.guard",
  "Lynx.Result.guardPassed",
  "Lynx.Result.handle",
  "Lynx.Result.instMonad",
  "Lynx.Result.instMonadExceptOfException",
  "Lynx.Result.instMonadStateOfEnvironment",
  "Lynx.Result.ofExcept",
  "Lynx.Result.ok",
  "Lynx.Result.receive",
  "Lynx.Result.receiveWith",
  "Lynx.Result.resolve",
  "Lynx.Result.resultCCPO",
  "Lynx.Result.run",
  "Lynx.Result.runWith",
  "Lynx.Result.schedule",
  "Lynx.Result.send",
  "Lynx.Result.set",
  "Lynx.Result.spawn",
  "Lynx.Result.toExcept",
  "Lynx.Result.toExceptRead",
  "Lynx.Result.tryWith",
  "Lynx.ScheduleChoice",
  "Lynx.ScheduleChoice.current",
  "Lynx.ScheduleChoice.swap",
  "Lynx.ScheduleChoice.timeout",
  "Lynx.Term",
  "Lynx.Term.Bitstring.Valid",
  "Lynx.Term.Bitstring.append",
  "Lynx.Term.Bitstring.binarySegment",
  "Lynx.Term.Bitstring.bitSize",
  "Lynx.Term.Bitstring.decodeInteger",
  "Lynx.Term.Bitstring.floatSegment",
  "Lynx.Term.Bitstring.instDecidableValid",
  "Lynx.Term.Bitstring.integerBits",
  "Lynx.Term.Bitstring.integerSegment",
  "Lynx.Term.Bitstring.matchBinary",
  "Lynx.Term.Bitstring.matchEnd",
  "Lynx.Term.Bitstring.matchFloat",
  "Lynx.Term.Bitstring.matchInteger",
  "Lynx.Term.Bitstring.matchTail",
  "Lynx.Term.Bitstring.matchUtf16",
  "Lynx.Term.Bitstring.matchUtf32",
  "Lynx.Term.Bitstring.matchUtf8",
  "Lynx.Term.Bitstring.ofBits",
  "Lynx.Term.Bitstring.pack",
  "Lynx.Term.Bitstring.toBits",
  "Lynx.Term.Bitstring.utf16Segment",
  "Lynx.Term.Bitstring.utf32Segment",
  "Lynx.Term.Bitstring.utf8Segment",
  "Lynx.Term.FiniteFloat",
  "Lynx.Term.FiniteFloat.add",
  "Lynx.Term.FiniteFloat.div",
  "Lynx.Term.FiniteFloat.exponent",
  "Lynx.Term.FiniteFloat.fraction",
  "Lynx.Term.FiniteFloat.magnitude",
  "Lynx.Term.FiniteFloat.mk",
  "Lynx.Term.FiniteFloat.mul",
  "Lynx.Term.FiniteFloat.negative",
  "Lynx.Term.FiniteFloat.ofInt",
  "Lynx.Term.FiniteFloat.ofScientific",
  "Lynx.Term.FiniteFloat.sub",
  "Lynx.Term.FiniteFloat.toRat",
  "Lynx.Term.Fun",
  "Lynx.Term.FunEntry",
  "Lynx.Term.FunEntry.effectful",
  "Lynx.Term.FunEntry.pure",
  "Lynx.Term.FunTable",
  "Lynx.Term.PureFun",
  "Lynx.Term.apply",
  "Lynx.Term.atom",
  "Lynx.Term.bitstring",
  "Lynx.Term.compare",
  "Lynx.Term.cons",
  "Lynx.Term.exactCompare",
  "Lynx.Term.false",
  "Lynx.Term.float",
  "Lynx.Term.function",
  "Lynx.Term.getMapKeys",
  "Lynx.Term.instDecidableEqFiniteFloat",
  "Lynx.Term.instReprFiniteFloat",
  "Lynx.Term.integer",
  "Lynx.Term.map",
  "Lynx.Term.nil",
  "Lynx.Term.pid",
  "Lynx.Term.reference",
  "Lynx.Term.true",
  "Lynx.Term.tuple",
  "Lynx.instBEqTerm",
  "Lynx.instCoeFunResultForallEnvironmentProdOutcome",
  "Lynx.instInhabitedEnvironment",
  "Lynx.instInhabitedProcessState",
  "Lynx.instInhabitedReceiveTimeout",
  "Lynx.instInhabitedScheduleChoice",
  "Lynx.instReprEnvironment",
  "Lynx.instReprException",
  "Lynx.instReprOutcome",
  "Lynx.instReprProcessState",
  "Lynx.instReprReceiveTimeout",
  "Lynx.instReprScheduleChoice",
  "Lynx.instReprTerm",
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
