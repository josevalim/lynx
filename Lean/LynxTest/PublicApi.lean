module

meta import Lean
public import Lynx.Runner
public import Lynx
public import Lynx.Modules.Erlang.erlang
public import Lynx.Modules.Erlang.binary
public import Lynx.Modules.Erlang.lists
public import Lynx.Modules.Erlang.maps
public import Lynx.Modules.Erlang.erts_internal
public import Lynx.Modules.Erlang.math
public import Lynx.Modules.Erlang.sets

-- Keep constructor and table adapter signatures part of the API check.
private def bitstringConstructor : (bytes : ByteArray) → (lastBits : Fin 8) →
    Lynx.Term.Bitstring.Valid bytes lastBits → Lynx.Term :=
  fun bytes lastBits valid => Lynx.Term.bitstring bytes lastBits valid
private def referenceConstructor : List Nat → Lynx.Term := Lynx.Term.reference
private def makeRef : Lynx.Result := Erlang.erlang.«make_ref/0» (Lynx.Dispatcher.ofTable [] 0)

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
    makeRef env = (.ok (.reference (env.currentPid ++ [env.refCounter + 1])),
      { env with refCounter := env.refCounter + 1 }) := by
  simp [makeRef]

private theorem makeRefContinuationEquation (next : Lynx.Term → Lynx.Result α)
    (env : Lynx.Environment) :
    (makeRef >>= next) env = next (.reference (env.currentPid ++ [env.refCounter + 1]))
      { env with refCounter := env.refCounter + 1 } := by
  simp [makeRef]
example : String → String → Nat → Array Lynx.Term → Lynx.Term := Lynx.Term.function
example (entry : Lynx.Dispatcher → Array Lynx.Term → Array Lynx.Term → Lynx.Result) :
    Lynx.Term.FunTable := [{ module := "m", name := "f", arity := 0, entry := .effectful entry }]
example (entry : Lynx.Dispatcher → Array Lynx.Term → Array Lynx.Term →
    Except Lynx.Exception Lynx.Term) :
    Lynx.Term.FunTable := [{ module := "m", name := "f", arity := 0, entry := .apply entry }]
example (entry : Array Lynx.Term → Array Lynx.Term → Except Lynx.Exception Lynx.Term) :
    Lynx.Term.FunTable := [{ module := "m", name := "f", arity := 0, entry := .pure entry }]

example : Lynx.Term.FunTable → Nat → Lynx.Dispatcher := Lynx.Dispatcher.ofTable
example : Lynx.Dispatcher → Lynx.Term → Array Lynx.Term → Except Lynx.Exception Lynx.Term :=
  Lynx.Dispatcher.pure
example : Lynx.Dispatcher → Lynx.Term → Array Lynx.Term → Lynx.Result := Lynx.Dispatcher.call
example : Lynx.Result → Lynx.Environment → Lynx.Outcome Lynx.Term × Lynx.Environment :=
  Lynx.Result.run
example : Lynx.Result → Lynx.Outcome Lynx.Term := fun computation => Lynx.sequential computation
example : Lynx.Dispatcher → Lynx.Term → Lynx.Term → Lynx.Result := Erlang.erlang.«apply/2»
example : Lynx.Dispatcher → Lynx.Term → Lynx.Term → Except Lynx.Exception Lynx.Term :=
  Erlang.erlang.«apply/2»
example : (Lynx.Dispatcher → Lynx.Term → Except Lynx.Exception Lynx.Term) →
    Lynx.Term.FunTable → Nat → Lynx.Term → Except Lynx.Exception Lynx.Term := Lynx.apply
example : Lynx.Dispatcher → Lynx.Term → Lynx.Result := Erlang.erlang.«spawn/1»
example : Lynx.Term → (Lynx.Environment → Lynx.Term → Option β) →
    (Option β → Lynx.Result α) → Lynx.Result α :=
  Lynx.Result.receiveWith
example : Lynx.PID → Lynx.ScheduleChoice := Lynx.ScheduleChoice.timeout
example : Lynx.Result → Lynx.Environment → List Lynx.ScheduleChoice →
    Lynx.Outcome Lynx.Term × Lynx.Environment :=
  fun computation env choices => computation.run env choices

-- Concurrent laws hold for every run, and checking proves them.
example (computation : Lynx.Result) (depth : Nat)
    (checked : ∀ elapsed,
      Lynx.Concurrent.check Lynx.Outcome.isTrue depth (.start {} computation elapsed) = true) :
    Lynx.concurrent computation (.ok Lynx.Term.true) :=
  Lynx.concurrent_of_check computation _ depth checked fun _ => Lynx.Outcome.eq_of_isTrue

-- No run goes on forever.
example : WellFounded fun next first : Lynx.Concurrent.Config Lynx.Term =>
    ∃ event, Lynx.Concurrent.Step first event next :=
  Lynx.Concurrent.Config.terminates

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

-- Table entries apply through the dispatcher, consuming depth unless pure.
example (table : Lynx.Term.FunTable) (depth arity : Nat) (module name : String)
    (captures arguments : Array Lynx.Term) (body : Array Lynx.Term → Lynx.Term.PureFun)
    (entry : Lynx.Dispatcher.find table module name arity = some (.pure body)) (size : arguments.size = arity) :
    (Lynx.Dispatcher.ofTable table depth).pure (.function module name arity captures) arguments =
      body captures arguments :=
  Lynx.Dispatcher.pure_pure entry size

example (table : Lynx.Term.FunTable) (depth arity : Nat) (module name : String)
    (captures arguments : Array Lynx.Term)
    (body : Lynx.Dispatcher → Array Lynx.Term → Lynx.Term.PureFun)
    (entry : Lynx.Dispatcher.find table module name arity = some (.apply body)) (size : arguments.size = arity) :
    (Lynx.Dispatcher.ofTable table (depth + 1)).pure (.function module name arity captures) arguments =
      body (Lynx.Dispatcher.ofTable table depth) captures arguments :=
  Lynx.Dispatcher.pure_apply entry size

example (table : Lynx.Term.FunTable) (depth arity : Nat) (module name : String)
    (captures arguments : Array Lynx.Term)
    (body : Lynx.Dispatcher → Array Lynx.Term → Lynx.Term.Fun)
    (entry : Lynx.Dispatcher.find table module name arity = some (.effectful body)) (size : arguments.size = arity) :
    (Lynx.Dispatcher.ofTable table (depth + 1)).call (.function module name arity captures) arguments =
      body (Lynx.Dispatcher.ofTable table depth) captures arguments :=
  Lynx.Dispatcher.call_effectful entry size

example (computation : Lynx.Result α) :
    (do let value ← computation; pure value) = computation := by
  simp

-- Ordinary guard evaluation supports environment reads without process effects.
example (dispatcher : Lynx.Dispatcher) (env : Lynx.Environment) :
    Lynx.Result.toExceptRead (Erlang.erlang.«self/0» dispatcher) env
        (Erlang.erlang.self_readOnly dispatcher) =
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
  "Erlang.binary.«last/1»",
  "Erlang.binary.«match/2»",
  "Erlang.binary.«match/3»",
  "Erlang.binary.«split/2»",
  "Erlang.binary.«split/3»",
  "Erlang.erlang.«*/2»",
  "Erlang.erlang.«++/2»",
  "Erlang.erlang.«+/1»",
  "Erlang.erlang.«+/2»",
  "Erlang.erlang.«--/2»",
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
  "Erlang.erlang.«apply/3»",
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
  "Erlang.erlang.«cancel_timer/1»",
  "Erlang.erlang.«ceil/1»",
  "Erlang.erlang.«demonitor/1»",
  "Erlang.erlang.«demonitor/2»",
  "Erlang.erlang.«div/2»",
  "Erlang.erlang.«element/2»",
  "Erlang.erlang.«erase/0»",
  "Erlang.erlang.«erase/1»",
  "Erlang.erlang.«error/2»",
  "Erlang.erlang.«error/3»",
  "Erlang.erlang.«exit/1»",
  "Erlang.erlang.«exit/2»",
  "Erlang.erlang.«float/1»",
  "Erlang.erlang.«float_to_binary/2»",
  "Erlang.erlang.«floor/1»",
  "Erlang.erlang.«fun_info_mfa/1»",
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
  "Erlang.erlang.«is_process_alive/1»",
  "Erlang.erlang.«is_reference/1»",
  "Erlang.erlang.«is_tuple/1»",
  "Erlang.erlang.«length/1»",
  "Erlang.erlang.«link/1»",
  "Erlang.erlang.«make_fun/3»",
  "Erlang.erlang.«make_ref/0»",
  "Erlang.erlang.«make_tuple/2»",
  "Erlang.erlang.«map_get/2»",
  "Erlang.erlang.«map_size/1»",
  "Erlang.erlang.«max/2»",
  "Erlang.erlang.«min/2»",
  "Erlang.erlang.«monitor/2»",
  "Erlang.erlang.«monitor/3»",
  "Erlang.erlang.«node/0»",
  "Erlang.erlang.«node/1»",
  "Erlang.erlang.«not/1»",
  "Erlang.erlang.«or/2»",
  "Erlang.erlang.«phash2/1»",
  "Erlang.erlang.«phash2/2»",
  "Erlang.erlang.«process_flag/2»",
  "Erlang.erlang.«process_info/2»",
  "Erlang.erlang.«put/2»",
  "Erlang.erlang.«raise/3»",
  "Erlang.erlang.«rem/2»",
  "Erlang.erlang.«round/1»",
  "Erlang.erlang.«self/0»",
  "Erlang.erlang.«send/2»",
  "Erlang.erlang.«send_after/3»",
  "Erlang.erlang.«send_after/4»",
  "Erlang.erlang.«setelement/3»",
  "Erlang.erlang.«size/1»",
  "Erlang.erlang.«spawn/1»",
  "Erlang.erlang.«spawn_link/1»",
  "Erlang.erlang.«spawn_monitor/1»",
  "Erlang.erlang.«throw/1»",
  "Erlang.erlang.«tl/1»",
  "Erlang.erlang.«trunc/1»",
  "Erlang.erlang.«tuple_size/1»",
  "Erlang.erlang.«unlink/1»",
  "Erlang.erlang.«xor/2»",
  "Erlang.erts_internal.«mc_iterator/1»",
  "Erlang.erts_internal.«mc_refill/1»",
  "Erlang.lists.«keyfind/3»",
  "Erlang.lists.«member/2»",
  "Erlang.lists.«reverse/2»",
  "Erlang.maps.«filter/2»",
  "Erlang.maps.«find/2»",
  "Erlang.maps.«fold/3»",
  "Erlang.maps.«from_keys/2»",
  "Erlang.maps.«from_list/1»",
  "Erlang.maps.«get/2»",
  "Erlang.maps.«intersect_with/3»",
  "Erlang.maps.«is_key/2»",
  "Erlang.maps.«iterator/1»",
  "Erlang.maps.«keys/1»",
  "Erlang.maps.«merge/2»",
  "Erlang.maps.«merge_with/3»",
  "Erlang.maps.«new/0»",
  "Erlang.maps.«next/1»",
  "Erlang.maps.«put/3»",
  "Erlang.maps.«remove/2»",
  "Erlang.maps.«take/2»",
  "Erlang.maps.«to_list/1»",
  "Erlang.maps.«update/3»",
  "Erlang.maps.«values/1»",
  "Erlang.math.«ceil/1»",
  "Erlang.math.«floor/1»",
  "Erlang.sets.elements?",
  "Erlang.sets.«from_list/1»",
  "Erlang.sets.«from_list/2»",
  "Erlang.sets.«intersection/2»",
  "Erlang.sets.«is_element/2»",
  "Erlang.sets.«is_subset/2»",
  "Erlang.sets.«new/0»",
  "Erlang.sets.«new/1»",
  "Erlang.sets.«size/1»",
  "Erlang.sets.«subtract/2»",
  "Erlang.sets.«union/2»",
  "Lynx.Concurrent.Config",
  "Lynx.Concurrent.Config.footprint",
  "Lynx.Concurrent.Config.forced",
  "Lynx.Concurrent.Config.independent",
  "Lynx.Concurrent.Config.outcome",
  "Lynx.Concurrent.Config.running",
  "Lynx.Concurrent.Config.start",
  "Lynx.Concurrent.Config.steps",
  "Lynx.Concurrent.Config.successors",
  "Lynx.Concurrent.Effect",
  "Lynx.Concurrent.Effect.andThen",
  "Lynx.Concurrent.Effect.apply",
  "Lynx.Concurrent.Effect.change",
  "Lynx.Concurrent.Effect.commutes",
  "Lynx.Concurrent.Effect.ending",
  "Lynx.Concurrent.Effect.inTransit",
  "Lynx.Concurrent.Effect.keeps",
  "Lynx.Concurrent.Effect.mk",
  "Lynx.Concurrent.Effect.record",
  "Lynx.Concurrent.Effect.records",
  "Lynx.Concurrent.Effect.send",
  "Lynx.Concurrent.Effect.timers",
  "Lynx.Concurrent.Envelope",
  "Lynx.Concurrent.Envelope.before",
  "Lynx.Concurrent.Envelope.between",
  "Lynx.Concurrent.Envelope.identical",
  "Lynx.Concurrent.Envelope.mk",
  "Lynx.Concurrent.Envelope.signal",
  "Lynx.Concurrent.Envelope.source",
  "Lynx.Concurrent.Envelope.target",
  "Lynx.Concurrent.Envelope.weight",
  "Lynx.Concurrent.Event",
  "Lynx.Concurrent.Event.bounce",
  "Lynx.Concurrent.Event.deliver",
  "Lynx.Concurrent.Event.exit",
  "Lynx.Concurrent.Event.fire",
  "Lynx.Concurrent.Event.internal",
  "Lynx.Concurrent.Event.receive",
  "Lynx.Concurrent.Event.request",
  "Lynx.Concurrent.Event.send",
  "Lynx.Concurrent.Event.spawn",
  "Lynx.Concurrent.Event.timeout",
  "Lynx.Concurrent.Failure",
  "Lynx.Concurrent.Failure.rejected",
  "Lynx.Concurrent.Failure.unfinished",
  "Lynx.Concurrent.Footprint",
  "Lynx.Concurrent.Footprint.bounce",
  "Lynx.Concurrent.Footprint.delivery",
  "Lynx.Concurrent.Footprint.effect",
  "Lynx.Concurrent.Footprint.ending",
  "Lynx.Concurrent.Footprint.fire",
  "Lynx.Concurrent.Footprint.independent",
  "Lynx.Concurrent.Footprint.mk",
  "Lynx.Concurrent.Footprint.observes",
  "Lynx.Concurrent.Footprint.spawn",
  "Lynx.Concurrent.Key",
  "Lynx.Concurrent.Key.beq",
  "Lynx.Concurrent.Key.bounce",
  "Lynx.Concurrent.Key.deliver",
  "Lynx.Concurrent.Key.fire",
  "Lynx.Concurrent.Key.own",
  "Lynx.Concurrent.Observes",
  "Lynx.Concurrent.Observes.and",
  "Lynx.Concurrent.Observes.inTransit",
  "Lynx.Concurrent.Observes.mk",
  "Lynx.Concurrent.Observes.record",
  "Lynx.Concurrent.Observes.records",
  "Lynx.Concurrent.Observes.timers",
  "Lynx.Concurrent.ProcessState",
  "Lynx.Concurrent.ProcessState.aliases",
  "Lynx.Concurrent.ProcessState.append",
  "Lynx.Concurrent.ProcessState.cancels",
  "Lynx.Concurrent.ProcessState.children",
  "Lynx.Concurrent.ProcessState.ending",
  "Lynx.Concurrent.ProcessState.env",
  "Lynx.Concurrent.ProcessState.identical",
  "Lynx.Concurrent.ProcessState.links",
  "Lynx.Concurrent.ProcessState.live",
  "Lynx.Concurrent.ProcessState.mailbox",
  "Lynx.Concurrent.ProcessState.mk",
  "Lynx.Concurrent.ProcessState.monitoring",
  "Lynx.Concurrent.ProcessState.monitors",
  "Lynx.Concurrent.ProcessState.pdict",
  "Lynx.Concurrent.ProcessState.receive",
  "Lynx.Concurrent.ProcessState.refCounter",
  "Lynx.Concurrent.ProcessState.trapExit",
  "Lynx.Concurrent.Run",
  "Lynx.Concurrent.Signal",
  "Lynx.Concurrent.Signal.aliasMessage",
  "Lynx.Concurrent.Signal.down",
  "Lynx.Concurrent.Signal.exit",
  "Lynx.Concurrent.Signal.identical",
  "Lynx.Concurrent.Signal.link",
  "Lynx.Concurrent.Signal.message",
  "Lynx.Concurrent.Signal.monitor",
  "Lynx.Concurrent.Signal.unlink",
  "Lynx.Concurrent.State",
  "Lynx.Concurrent.State.alive",
  "Lynx.Concurrent.State.allocate",
  "Lynx.Concurrent.State.append",
  "Lynx.Concurrent.State.bounce",
  "Lynx.Concurrent.State.elapsed",
  "Lynx.Concurrent.State.emit",
  "Lynx.Concurrent.State.exitSignal",
  "Lynx.Concurrent.State.fire",
  "Lynx.Concurrent.State.firing",
  "Lynx.Concurrent.State.inTransit",
  "Lynx.Concurrent.State.initial",
  "Lynx.Concurrent.State.mk",
  "Lynx.Concurrent.State.modify",
  "Lynx.Concurrent.State.process",
  "Lynx.Concurrent.State.processes",
  "Lynx.Concurrent.State.receive",
  "Lynx.Concurrent.State.request",
  "Lynx.Concurrent.State.spawn",
  "Lynx.Concurrent.State.spawnWith",
  "Lynx.Concurrent.State.store",
  "Lynx.Concurrent.State.terminate",
  "Lynx.Concurrent.State.timers",
  "Lynx.Concurrent.State.update",
  "Lynx.Concurrent.State.view",
  "Lynx.Concurrent.State.weight",
  "Lynx.Concurrent.Step",
  "Lynx.Concurrent.Task",
  "Lynx.Concurrent.Task.child",
  "Lynx.Concurrent.Task.computation",
  "Lynx.Concurrent.Task.deliveries",
  "Lynx.Concurrent.Task.delivery",
  "Lynx.Concurrent.Task.ended",
  "Lynx.Concurrent.Task.finish",
  "Lynx.Concurrent.Task.footprint",
  "Lynx.Concurrent.Task.keyed",
  "Lynx.Concurrent.Task.local",
  "Lynx.Concurrent.Task.mk",
  "Lynx.Concurrent.Task.own",
  "Lynx.Concurrent.Task.root",
  "Lynx.Concurrent.Task.transitions",
  "Lynx.Concurrent.Task.β",
  "Lynx.Concurrent.Terminal",
  "Lynx.Concurrent.Timer",
  "Lynx.Concurrent.Timer.destination",
  "Lynx.Concurrent.Timer.duration",
  "Lynx.Concurrent.Timer.identical",
  "Lynx.Concurrent.Timer.message",
  "Lynx.Concurrent.Timer.mk",
  "Lynx.Concurrent.Timer.reference",
  "Lynx.Concurrent.Transition",
  "Lynx.Concurrent.Transition.apply",
  "Lynx.Concurrent.Transition.event",
  "Lynx.Concurrent.Transition.exhausted",
  "Lynx.Concurrent.Transition.finished",
  "Lynx.Concurrent.Transition.mk",
  "Lynx.Concurrent.Transition.state",
  "Lynx.Concurrent.Transition.tasks",
  "Lynx.Concurrent.arrive",
  "Lynx.Concurrent.check",
  "Lynx.Concurrent.checkFrom",
  "Lynx.Concurrent.clock",
  "Lynx.Concurrent.counterexample",
  "Lynx.Concurrent.counterexampleFrom",
  "Lynx.Concurrent.deliverable",
  "Lynx.Concurrent.deliverableFrom",
  "Lynx.Concurrent.enqueue",
  "Lynx.Concurrent.exitReason",
  "Lynx.Concurrent.explore",
  "Lynx.Concurrent.exploreFind",
  "Lynx.Concurrent.firstOfEach",
  "Lynx.Concurrent.firstTimer",
  "Lynx.Concurrent.identicalLists",
  "Lynx.Concurrent.insertOnce",
  "Lynx.Concurrent.insertTimer",
  "Lynx.Concurrent.instBEqKey",
  "Lynx.Concurrent.instDecidableEqKey",
  "Lynx.Concurrent.instInhabitedProcessState",
  "Lynx.Concurrent.instReprEnvelope",
  "Lynx.Concurrent.instReprEvent",
  "Lynx.Concurrent.instReprProcessState",
  "Lynx.Concurrent.instReprSignal",
  "Lynx.Concurrent.instReprTimer",
  "Lynx.Concurrent.isKill",
  "Lynx.Concurrent.isMonitorMessage",
  "Lynx.Concurrent.isNormal",
  "Lynx.Concurrent.isRequest",
  "Lynx.Concurrent.oldest",
  "Lynx.Concurrent.pidBefore",
  "Lynx.Concurrent.recordIdentical",
  "Lynx.Concurrent.remaining",
  "Lynx.Concurrent.report",
  "Lynx.Concurrent.requestFootprint",
  "Lynx.Concurrent.selectMessage",
  "Lynx.Concurrent.selected",
  "Lynx.Concurrent.splits",
  "Lynx.Dispatch",
  "Lynx.Dispatch.dispatch",
  "Lynx.Dispatch.mk",
  "Lynx.Dispatcher",
  "Lynx.Dispatcher.badarity",
  "Lynx.Dispatcher.badfun",
  "Lynx.Dispatcher.call",
  "Lynx.Dispatcher.find",
  "Lynx.Dispatcher.inner",
  "Lynx.Dispatcher.lookup",
  "Lynx.Dispatcher.mk",
  "Lynx.Dispatcher.named",
  "Lynx.Dispatcher.ofTable",
  "Lynx.Dispatcher.pure",
  "Lynx.Dispatcher.resolve",
  "Lynx.Dispatcher.step",
  "Lynx.Environment",
  "Lynx.Environment.currentPid",
  "Lynx.Environment.mk",
  "Lynx.Environment.pdict",
  "Lynx.Environment.refCounter",
  "Lynx.Except.andAlso",
  "Lynx.Except.bindWith",
  "Lynx.Except.cutoff",
  "Lynx.Except.guard",
  "Lynx.Except.guardPassed",
  "Lynx.Except.instCCPO",
  "Lynx.Except.instPartialOrder",
  "Lynx.Except.isExhausted",
  "Lynx.Except.orElse",
  "Lynx.Except.tryWith",
  "Lynx.Exception",
  "Lynx.Exception.classTerm",
  "Lynx.Exception.error",
  "Lynx.Exception.exhausted",
  "Lynx.Exception.exit",
  "Lynx.Exception.reason",
  "Lynx.Exception.stacktrace",
  "Lynx.Exception.throw",
  "Lynx.Exception.withReason",
  "Lynx.Outcome",
  "Lynx.Outcome.deadlock",
  "Lynx.Outcome.error",
  "Lynx.Outcome.isTrue",
  "Lynx.Outcome.ok",
  "Lynx.PID",
  "Lynx.ReceiveTimeout",
  "Lynx.ReceiveTimeout.finite",
  "Lynx.ReceiveTimeout.immediate",
  "Lynx.ReceiveTimeout.infinity",
  "Lynx.ReceiveTimeout.ofTerm",
  "Lynx.Request",
  "Lynx.Request.alive",
  "Lynx.Request.cancelTimer",
  "Lynx.Request.demonitor",
  "Lynx.Request.exit",
  "Lynx.Request.link",
  "Lynx.Request.monitor",
  "Lynx.Request.sendAlias",
  "Lynx.Request.startTimer",
  "Lynx.Request.trapExit",
  "Lynx.Request.unlink",
  "Lynx.Result",
  "Lynx.Result.IsPure",
  "Lynx.Result.IsReadOnly",
  "Lynx.Result.andAlso",
  "Lynx.Result.bind",
  "Lynx.Result.error",
  "Lynx.Result.get",
  "Lynx.Result.guard",
  "Lynx.Result.guardPassed",
  "Lynx.Result.handle",
  "Lynx.Result.instMonad",
  "Lynx.Result.instMonadExceptOfException",
  "Lynx.Result.instMonadStateOfEnvironment",
  "Lynx.Result.isExhausted",
  "Lynx.Result.ofExcept",
  "Lynx.Result.ofExceptWith",
  "Lynx.Result.ok",
  "Lynx.Result.orElse",
  "Lynx.Result.receive",
  "Lynx.Result.receiveWith",
  "Lynx.Result.request",
  "Lynx.Result.resultCCPO",
  "Lynx.Result.run",
  "Lynx.Result.schedule",
  "Lynx.Result.send",
  "Lynx.Result.set",
  "Lynx.Result.toExcept",
  "Lynx.Result.toExceptRead",
  "Lynx.Result.tryWith",
  "Lynx.ScheduleChoice",
  "Lynx.ScheduleChoice.current",
  "Lynx.ScheduleChoice.swap",
  "Lynx.ScheduleChoice.timeout",
  "Lynx.SpawnOptions",
  "Lynx.SpawnOptions.link",
  "Lynx.SpawnOptions.mk",
  "Lynx.SpawnOptions.monitor",
  "Lynx.Term",
  "Lynx.Term.Bitstring.Measure.bytes",
  "Lynx.Term.Bitstring.Measure.lastBits",
  "Lynx.Term.Bitstring.Valid",
  "Lynx.Term.Bitstring.append",
  "Lynx.Term.Bitstring.binarySegment",
  "Lynx.Term.Bitstring.bitSize",
  "Lynx.Term.Bitstring.decodeInteger",
  "Lynx.Term.Bitstring.extract",
  "Lynx.Term.Bitstring.extractWith",
  "Lynx.Term.Bitstring.floatSegment",
  "Lynx.Term.Bitstring.floatWidth",
  "Lynx.Term.Bitstring.instDecidableValid",
  "Lynx.Term.Bitstring.integerBits",
  "Lynx.Term.Bitstring.integerSegment",
  "Lynx.Term.Bitstring.matchBinary",
  "Lynx.Term.Bitstring.matchEnd",
  "Lynx.Term.Bitstring.matchFloat",
  "Lynx.Term.Bitstring.matchInteger",
  "Lynx.Term.Bitstring.matchNarrowFloat",
  "Lynx.Term.Bitstring.matchTail",
  "Lynx.Term.Bitstring.matchUtf16",
  "Lynx.Term.Bitstring.matchUtf32",
  "Lynx.Term.Bitstring.matchUtf8",
  "Lynx.Term.Bitstring.narrowFloatSegment",
  "Lynx.Term.Bitstring.ofBits",
  "Lynx.Term.Bitstring.pack",
  "Lynx.Term.Bitstring.toBits",
  "Lynx.Term.Bitstring.utf16Segment",
  "Lynx.Term.Bitstring.utf32Segment",
  "Lynx.Term.Bitstring.utf8Segment",
  "Lynx.Term.Bitstring.zeroWidth",
  "Lynx.Term.Compare.compareMapViews",
  "Lynx.Term.Compare.compareOn",
  "Lynx.Term.Compare.compareStep",
  "Lynx.Term.Compare.exactFloatCompare",
  "Lynx.Term.Compare.exactFloatCompareSlow",
  "Lynx.Term.Compare.mapView",
  "Lynx.Term.Compare.mapViewInsert",
  "Lynx.Term.Compare.ratCompare",
  "Lynx.Term.FiniteFloat",
  "Lynx.Term.FiniteFloat.add",
  "Lynx.Term.FiniteFloat.binary16",
  "Lynx.Term.FiniteFloat.div",
  "Lynx.Term.FiniteFloat.exponent",
  "Lynx.Term.FiniteFloat.fraction",
  "Lynx.Term.FiniteFloat.magnitude",
  "Lynx.Term.FiniteFloat.mk",
  "Lynx.Term.FiniteFloat.mul",
  "Lynx.Term.FiniteFloat.narrow",
  "Lynx.Term.FiniteFloat.narrowInt",
  "Lynx.Term.FiniteFloat.negative",
  "Lynx.Term.FiniteFloat.ofInt",
  "Lynx.Term.FiniteFloat.ofScientific",
  "Lynx.Term.FiniteFloat.sub",
  "Lynx.Term.FiniteFloat.toRat",
  "Lynx.Term.FiniteFloat.widen",
  "Lynx.Term.Fun",
  "Lynx.Term.FunDef",
  "Lynx.Term.FunDef.arity",
  "Lynx.Term.FunDef.entry",
  "Lynx.Term.FunDef.mk",
  "Lynx.Term.FunDef.module",
  "Lynx.Term.FunDef.name",
  "Lynx.Term.FunEntry",
  "Lynx.Term.FunEntry.apply",
  "Lynx.Term.FunEntry.effectful",
  "Lynx.Term.FunEntry.pure",
  "Lynx.Term.FunTable",
  "Lynx.Term.PureFun",
  "Lynx.Term.atom",
  "Lynx.Term.bitstring",
  "Lynx.Term.compare",
  "Lynx.Term.cons",
  "Lynx.Term.demonitorOptions",
  "Lynx.Term.exactCompare",
  "Lynx.Term.false",
  "Lynx.Term.float",
  "Lynx.Term.function",
  "Lynx.Term.getMapKeys",
  "Lynx.Term.identical",
  "Lynx.Term.identicalEntries",
  "Lynx.Term.identicalList",
  "Lynx.Term.insertions",
  "Lynx.Term.instDecidableEqFiniteFloat",
  "Lynx.Term.instReprFiniteFloat",
  "Lynx.Term.integer",
  "Lynx.Term.isMember",
  "Lynx.Term.isProperList",
  "Lynx.Term.keysDistinct",
  "Lynx.Term.list",
  "Lynx.Term.map",
  "Lynx.Term.mapEntries",
  "Lynx.Term.mapEnumeration",
  "Lynx.Term.mapLookup",
  "Lynx.Term.monitorAlias",
  "Lynx.Term.nil",
  "Lynx.Term.orders",
  "Lynx.Term.pairList?",
  "Lynx.Term.pid",
  "Lynx.Term.properList?",
  "Lynx.Term.reference",
  "Lynx.Term.sendAfter",
  "Lynx.Term.timerAbsolute",
  "Lynx.Term.true",
  "Lynx.Term.tuple",
  "Lynx.apply",
  "Lynx.concurrent",
  "Lynx.instBEqTerm",
  "Lynx.instCoeFunResultForallEnvironmentProdOutcome",
  "Lynx.instDispatchExceptException",
  "Lynx.instDispatchResult",
  "Lynx.instInhabitedEnvironment",
  "Lynx.instInhabitedException",
  "Lynx.instInhabitedReceiveTimeout",
  "Lynx.instInhabitedScheduleChoice",
  "Lynx.instInhabitedSpawnOptions",
  "Lynx.instReprEnvironment",
  "Lynx.instReprException",
  "Lynx.instReprOutcome",
  "Lynx.instReprReceiveTimeout",
  "Lynx.instReprRequest",
  "Lynx.instReprScheduleChoice",
  "Lynx.instReprSpawnOptions",
  "Lynx.instReprTerm",
  "Lynx.sequential",
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
