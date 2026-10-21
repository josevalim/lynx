module

meta import LynxTest.ProofAudit
import Lynx
import Lynx.Modules.Erlang.erlang
import all Lynx.Term
import all Lynx.Term.DataTypes
import all Lynx.Term.Dispatch
import all Lynx.Term.Runner

namespace LynxTest.Term.Dispatch
open Lynx

private def countdown : Term.FunTable := #[.effectful fun dispatcher _ (args : Array Term) =>
  match args[0]? with
  | some (Term.integer n) =>
      if n ≤ 0 then .ok (.integer 0)
      else dispatcher.call (.function 0 1 #[]) #[.integer (n - 1)]
  | _ => .error (.error (.atom "badarg"))]

/-- A recursive table requires no recursive Lean definition or cyclic import. -/
theorem recursive_dispatch :
    ((Dispatcher.ofTable countdown 4).call (.function 0 1 #[]) #[.integer 3]).run {} =
      (.ok (.integer 0), {}) ∧
    ((Dispatcher.ofTable countdown 3).call (.function 0 1 #[]) #[.integer 3]).run {} =
      (.error .exhausted, {}) := by
  repeat' apply And.intro
  all_goals first | exact rfl | (cbv <;> rfl)

private def constant : Term.FunTable := #[.effectful fun _ _ _ => .ok (.integer 7)]

private def pureFunctions : Term.FunTable := #[
  .pure fun captures arguments =>
    match captures.toList, arguments.toList with
    | [.integer captured], [.integer argument] => .ok (.integer (captured + argument))
    | _, _ => .error (.throw (.atom "bad_input")),
  .effectful fun _ _ _ => .get fun env => .ok (.pid env.currentPid)
]

/-- Pure and effectful calls dispatch pure closures, including captures and exceptions. -/
theorem pure_calls :
    (Dispatcher.ofTable pureFunctions 0).pure (.function 0 1 #[.integer 10]) #[.integer 7] =
      .ok (.integer 17) ∧
    (Dispatcher.ofTable pureFunctions 0).pure (.function 0 1 #[]) #[.integer 7] =
      .error (.throw (.atom "bad_input")) ∧
    (Dispatcher.ofTable pureFunctions 0).pure (.function 0 1 #[]) #[] =
      .error (.error (.tuple #[.atom "badarity", .tuple #[.function 0 1 #[], .nil]])) ∧
    (Dispatcher.ofTable pureFunctions 0).pure (.function 9 0 #[]) #[] =
      .error (.error (.tuple #[.atom "badfun", .function 9 0 #[]])) ∧
    (Dispatcher.ofTable pureFunctions 0).call (.atom "not_a_fun") #[] =
      .error (.error (.tuple #[.atom "badfun", .atom "not_a_fun"])) := by
  repeat' apply And.intro
  all_goals cbv

/-- Pure entries run without a dispatch budget, inside the caller's handlers. -/
theorem pure_dispatch_without_depth :
    ((Dispatcher.ofTable pureFunctions 0).call (.function 0 1 #[.integer 10]) #[.integer 7]).run {} =
      (.ok (.integer 17), {}) ∧
    (Result.handle ((Dispatcher.ofTable pureFunctions 0).call (.function 0 1 #[]) #[.integer 7])
      (fun _ => .ok (.atom "caught"))).run {} =
      (.ok (.atom "caught"), {}) := by
  constructor <;> cbv

/-- An effectful entry consumes one level of depth, and does not return from pure callers. -/
theorem effectful_call :
    ((Dispatcher.ofTable pureFunctions 1).call (.function 1 0 #[]) #[]).run {} =
      (.ok (.pid 1), {}) ∧
    ((Dispatcher.ofTable pureFunctions 0).call (.function 1 0 #[]) #[]).run {} =
      (.error .exhausted, {}) ∧
    (Dispatcher.ofTable pureFunctions 1).pure (.function 1 0 #[]) #[] = .error .exhausted := by
  repeat' apply And.intro
  all_goals cbv

private def dispatching : Term.FunTable := #[
  .pure fun _ arguments =>
    match arguments.toList with
    | [.integer argument] => .ok (.integer (argument + 1))
    | _ => .error (.error (.atom "badarg")),
  .apply fun dispatcher _ arguments =>
    match arguments.toList with
    | [argument] => dispatcher.pure (.function 0 1 #[]) #[argument]
    | _ => .error (.error (.atom "badarg"))
]

/-- Entries that dispatch further consume one level of depth when called purely. -/
theorem apply_call :
    (Dispatcher.ofTable dispatching 1).pure (.function 1 1 #[]) #[.integer 1] = .ok (.integer 2) ∧
    (Dispatcher.ofTable dispatching 0).pure (.function 1 1 #[]) #[.integer 1] = .error .exhausted ∧
    ((Dispatcher.ofTable dispatching 1).call (.function 1 1 #[]) #[.integer 1]).run {} =
      (.ok (.integer 2), {}) := by
  repeat' apply And.intro
  all_goals cbv

/-- Sequential calls reuse the depth budget after returning. -/
theorem sequential_dispatch :
    (do let _ ← (Dispatcher.ofTable constant 1).call (.function 0 0 #[]) #[]
        (Dispatcher.ofTable constant 1).call (.function 0 0 #[]) #[]).run {} =
      (.ok (.integer 7), {}) ∧
    ((Dispatcher.ofTable constant 0).call (.function 0 0 #[]) #[]).run {} =
      (.error .exhausted, {}) ∧
    ((Dispatcher.ofTable constant 0).call (.function 1 0 #[]) #[]).run {} =
      (.error (.error (.tuple #[.atom "badfun", .function 1 0 #[]])), {}) := by
  repeat' apply And.intro
  all_goals first | exact rfl | (cbv <;> rfl)

private def failing : Term.FunTable := #[.effectful fun _ _ _ => .error (.throw (.integer 9))]

/-- Exceptions raised inside dispatched code reach the caller's handler. -/
theorem catch_dispatched_exception :
    (Result.handle ((Dispatcher.ofTable failing 1).call (.function 0 0 #[]) #[])
      (fun _ => .ok (.integer 42))).run {} = (.ok (.integer 42), {}) := by
  first | exact rfl | (cbv <;> rfl)

/-- Exhaustion cannot be caught as an Erlang exception. -/
theorem exhaustion_is_not_an_exception :
    (Result.handle ((Dispatcher.ofTable failing 0).call (.function 0 0 #[]) #[])
      (fun _ => .ok (.integer 42))).run {} = (.error .exhausted, {}) := by
  first | exact rfl | (cbv <;> rfl)

private def stateful : Term.FunTable := #[.effectful fun _ _ _ =>
  .get fun env => .set { env with currentProcess.pdict := [(.atom "key", .integer 1)] }
    (.ok (.integer 7))]

/-- Dispatch preserves state changes for the caller's continuation. -/
theorem dispatched_state :
    (do let _ ← (Dispatcher.ofTable stateful 1).call (.function 0 0 #[]) #[]
        getThe Environment).run {} =
      (.ok { currentProcess.pdict := [(.atom "key", .integer 1)] },
        { currentProcess.pdict := [(.atom "key", .integer 1)] }) := by
  first | exact rfl | (cbv <;> rfl)

/-- Children receive the dispatcher without adding a scheduling boundary. -/
theorem spawned_dispatch :
    (Result.schedule ((Dispatcher.ofTable
        #[.effectful fun _ _ _ => .send 1 (.integer 7) (.ok .nil)] 1).call (.function 0 0 #[]) #[])
      fun _ => .receive .infinity (fun _ value => some value) (fun value => .ok (value.getD .nil))).run {} =
      (.ok (.integer 7), { pidCounter := 2 }) := by cbv

/-- Pure bodies may be spawned; this still creates a child and a scheduling boundary. -/
theorem pure_spawn_without_depth :
    (Erlang.erlang.«spawn/1» (Dispatcher.ofTable #[.pure fun _ _ => .ok (.integer 7)] 0)
      (.function 0 0 #[])).run {} =
      (.ok (.pid 2), { pidCounter := 2 }) := by cbv

/-- Values that are not zero-arity functions fail in the caller without allocating a
child. A child calling a function value the table does not contain fails on its own,
and exceptions raised by a child do not reach the caller's exception handler. -/
theorem spawn_exception_boundaries :
    (Result.handle (Erlang.erlang.«spawn/1» (Dispatcher.ofTable failing 1) (.atom "not_a_fun"))
      (fun _ => .ok (.atom "caught"))).run {} = (.ok (.atom "caught"), {}) ∧
    (Result.handle (Erlang.erlang.«spawn/1» (Dispatcher.ofTable failing 1) (.function 9 0 #[]))
      (fun _ => .ok (.atom "caught"))).run {} = (.ok (.pid 2), { pidCounter := 2 }) ∧
    (Result.handle (Erlang.erlang.«spawn/1» (Dispatcher.ofTable failing 1) (.function 0 0 #[]))
      (fun _ => .ok (.atom "caught"))).run {} = (.ok (.pid 2), { pidCounter := 2 }) := by
  refine ⟨?_, ?_, ?_⟩ <;> cbv

/-- Recursive spawning consumes dispatch depth rather than resetting the budget
for each new process. The child exceeding it ends the run. -/
theorem recursive_spawn_exhausts :
    match (Erlang.erlang.«spawn/1» (Dispatcher.ofTable #[.effectful fun dispatcher _ _ =>
        Erlang.erlang.«spawn/1» dispatcher (.function 0 0 #[])] 3) (.function 0 0 #[])).run {} with
    | (.error .exhausted, env) => env.pidCounter = 5
    | _ => False := by cbv

end LynxTest.Term.Dispatch

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Term.Dispatch
  LynxTest.ProofAudit.checkModule `LynxTest.Term.Dispatch
