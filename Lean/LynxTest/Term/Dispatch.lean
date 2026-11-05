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
      (.ok (.pid []), {}) ∧
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
  .get fun env => .set { env with pdict := [(.atom "key", .integer 1)] }
    (.ok (.integer 7))]

/-- Dispatch preserves state changes for the caller's continuation. -/
theorem dispatched_state :
    (do let _ ← (Dispatcher.ofTable stateful 1).call (.function 0 0 #[]) #[]
        getThe Environment).run {} =
      (.ok { pdict := [(.atom "key", .integer 1)] },
        { pdict := [(.atom "key", .integer 1)] }) := by
  first | exact rfl | (cbv <;> rfl)

/-- Children receive the dispatcher without adding a scheduling boundary. -/
theorem spawned_dispatch :
    (Result.schedule {} ((Dispatcher.ofTable
        #[.effectful fun _ _ _ => .send [] (.integer 7) (.ok .nil)] 1).call (.function 0 0 #[]) #[])
      fun _ => .receive .infinity (fun _ value => some value) (fun value => .ok (value.getD .nil))).run {} =
      (.ok (.integer 7), {}) := by cbv

/-- Pure bodies may be spawned; this still creates a child and a scheduling boundary. -/
theorem pure_spawn_without_depth :
    (Erlang.erlang.«spawn/1» (Dispatcher.ofTable #[.pure fun _ _ => .ok (.integer 7)] 0)
      (.function 0 0 #[])).run {} =
      (.ok (.pid [1]), {}) := by cbv

/-- Values that are not zero-arity functions fail in the caller without allocating a
child. A child calling a function value the table does not contain fails on its own,
and exceptions raised by a child do not reach the caller's exception handler. -/
theorem spawn_exception_boundaries :
    (Result.handle (Erlang.erlang.«spawn/1» (Dispatcher.ofTable failing 1) (.atom "not_a_fun"))
      (fun _ => .ok (.atom "caught"))).run {} = (.ok (.atom "caught"), {}) ∧
    (Result.handle (Erlang.erlang.«spawn/1» (Dispatcher.ofTable failing 1) (.function 9 0 #[]))
      (fun _ => .ok (.atom "caught"))).run {} = (.ok (.pid [1]), {}) ∧
    (Result.handle (Erlang.erlang.«spawn/1» (Dispatcher.ofTable failing 1) (.function 0 0 #[]))
      (fun _ => .ok (.atom "caught"))).run {} = (.ok (.pid [1]), {}) := by
  refine ⟨?_, ?_, ?_⟩ <;> cbv

/-- Recursive spawning consumes dispatch depth rather than resetting the budget
for each new process. The child exceeding it ends the run. -/
theorem recursive_spawn_exhausts :
    match (Erlang.erlang.«spawn/1» (Dispatcher.ofTable #[.effectful fun dispatcher _ _ =>
        Erlang.erlang.«spawn/1» dispatcher (.function 0 0 #[])] 3) (.function 0 0 #[])).run {} with
    | (.error .exhausted, _) => True
    | _ => False := by cbv

/-- Entries can record the name the compiler gave their function. -/
private def named : Term.FunTable := #[
  .pure (fun _ _ => .ok .nil) (some (.tuple #[.atom "example", .atom "-f/1-fun-0-", .integer 0])),
  .pure fun _ _ => .ok .nil]

theorem fun_info_mfa_reports_compiled_name :
    (Erlang.erlang.«fun_info_mfa/1» (Dispatcher.ofTable named 1) (.function 0 0 #[]) :
      Except Exception Term) = .ok (.tuple #[.atom "example", .atom "-f/1-fun-0-", .integer 0]) ∧
    (Erlang.erlang.«fun_info_mfa/1» (Dispatcher.ofTable named 1) (.function 1 0 #[]) :
      Except Exception Term) = .error .exhausted ∧
    (Erlang.erlang.«fun_info_mfa/1» (Dispatcher.ofTable named 1) (.atom "not_a_fun") :
      Except Exception Term) = .error (.error (.atom "badarg")) := by
  refine ⟨?_, ?_, ?_⟩ <;> cbv

/-- A local function, and `fun erlang:apply/2`. -/
private def byName : Term.FunTable := #[
  .pure (fun _ _ => .ok (.atom "done")) (some (.tuple #[.atom "example", .atom "done", .integer 0])),
  .apply (fun dispatcher captures args =>
      match captures.toList, args.toList with
      | [], [function, arguments] => Erlang.erlang.«apply/2» dispatcher function arguments
      | _, _ => .error (.error (.atom "badarg")))
    (some (.tuple #[.atom "erlang", .atom "apply", .integer 2]))]

/-- Calls by name find entries by the name and arity they record. -/
theorem resolve_finds_named_entries :
    (Dispatcher.ofTable byName 1).resolve (.atom "erlang") (.atom "apply") 2 =
      some (.function 1 2 #[]) ∧
    (Dispatcher.ofTable byName 1).resolve (.atom "example") (.atom "done") 0 =
      some (.function 0 0 #[]) ∧
    (Dispatcher.ofTable byName 1).resolve (.atom "erlang") (.atom "apply") 3 = none := by
  refine ⟨?_, ?_, ?_⟩ <;> cbv

theorem apply_calls_by_name :
    (Erlang.erlang.«apply/3» (Dispatcher.ofTable byName 2) (.atom "erlang") (.atom "apply")
      (.cons (.function 0 0 #[]) (.cons .nil .nil)) : Except Exception Term) = .ok (.atom "done") ∧
    (Erlang.erlang.«apply/3» (Dispatcher.ofTable byName 2) (.atom "example") (.atom "missing")
      .nil : Except Exception Term) = .error .exhausted ∧
    (Erlang.erlang.«apply/3» (Dispatcher.ofTable byName 2) (.integer 1) (.atom "done")
      .nil : Except Exception Term) = .error (.error (.atom "badarg")) := by
  refine ⟨?_, ?_, ?_⟩ <;> cbv

theorem make_fun_resolves_by_name :
    (Erlang.erlang.«make_fun/3» (Dispatcher.ofTable byName 1) (.atom "erlang") (.atom "apply")
      (.integer 2) : Except Exception Term) = .ok (.function 1 2 #[]) ∧
    (Erlang.erlang.«make_fun/3» (Dispatcher.ofTable byName 1) (.atom "example") (.atom "missing")
      (.integer 0) : Except Exception Term) = .error .exhausted ∧
    (Erlang.erlang.«make_fun/3» (Dispatcher.ofTable byName 1) (.atom "erlang") (.atom "apply")
      (.integer (-1)) : Except Exception Term) = .error (.error (.atom "badarg")) := by
  refine ⟨?_, ?_, ?_⟩ <;> cbv

end LynxTest.Term.Dispatch

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Term.Dispatch
  LynxTest.ProofAudit.checkModule `LynxTest.Term.Dispatch
