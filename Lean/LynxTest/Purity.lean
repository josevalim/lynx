module

import Lynx.Modules.Erlang.erlang
import Lynx
meta import LynxTest.ProofAudit

namespace LynxTest.Purity
open Lynx

-- The coercion exposes only the named operation, not the scheduler body.
theorem callable_result (computation : Result) (env : Environment) :
    computation env = computation.run env := rfl

theorem run_ok (value : Term) (env : Environment) :
    (Result.ok value).run env = (.ok value, env) := by simp

theorem one_bit_size :
    Erlang.erlang.«bit_size/1» (.bitstring ⟨#[128]⟩ 1) = .ok (.integer 1) := by
  rfl

theorem float_zero_value :
    Term.FiniteFloat.toRat ⟨false, 0, 0⟩ = 0 := rfl

-- The integer shortcut must retain symbolic float and mixed-addition proofs.
theorem float_addition (left right result : Term.FiniteFloat)
    (sum : left.add right = some result) :
    Erlang.erlang.«+/2» (.float left) (.float right) = .ok (.float result) := by
  simp [Erlang.erlang.«+/2_floats», sum]

theorem mixed_addition (integer : Int) (converted right result : Term.FiniteFloat)
    (conversion : Term.FiniteFloat.ofInt integer = some converted)
    (sum : converted.add right = some result) :
    Erlang.erlang.«+/2» (.integer integer) (.float right) = .ok (.float result) := by
  simp [conversion, sum]

theorem mixed_addition_reversed (integer : Int) (converted left result : Term.FiniteFloat)
    (conversion : Term.FiniteFloat.ofInt integer = some converted)
    (sum : left.add converted = some result) :
    Erlang.erlang.«+/2» (.float left) (.integer integer) = .ok (.float result) := by
  simp [conversion, sum]


theorem binary_is_bitstring (input : Term)
    (accepted : Erlang.erlang.«is_binary/1» input = .ok Term.true) :
    Erlang.erlang.«is_bitstring/1» input = .ok Term.true := by
  cases input <;> simp_all [Erlang.erlang.«is_binary/1»,
    Erlang.erlang.«is_bitstring/1», Term.true, Term.false]

theorem bitstring_size_is_integer (input : Term)
    (accepted : Erlang.erlang.«is_bitstring/1» input = .ok Term.true) :
    (do let size ← Erlang.erlang.«bit_size/1» input
        Erlang.erlang.«is_integer/1» size) = .ok Term.true := by
  cases input <;> simp_all [Erlang.erlang.«is_bitstring/1»,
    Erlang.erlang.«bit_size/1», Erlang.erlang.«is_integer/1», Term.true, Term.false]

theorem bitstring_byte_size_is_integer (input : Term)
    (accepted : Erlang.erlang.«is_bitstring/1» input = .ok Term.true) :
    (do let size ← Erlang.erlang.«byte_size/1» input
        Erlang.erlang.«is_integer/1» size) = .ok Term.true := by
  cases input <;> simp_all [Erlang.erlang.«is_bitstring/1»,
    Erlang.erlang.«byte_size/1», Erlang.erlang.«is_integer/1», Term.true, Term.false]

-- Pure functions return `Except`, so they need no purity proof. A guard
-- continuation contains one flat recursive suffix, whose functional induction
-- sees the guard's cases.
private def guardedSuffix (input : Term) : Except Exception Term :=
  (fun {α : Type} (body : (Unit → Except Exception α) → Except Exception α)
      (next : Unit → Except Exception α) => body next)
  (fun next => Except.tryWith (Erlang.erlang.«is_integer/1» input)
    (fun value => match value with
      | .atom "true" => .ok (.integer 0)
      | _ => next ())
    (fun _ => next ()))
    (fun (_ : Unit) => match input with
      | .nil => .ok (.integer 0)
      | .cons _ tail => guardedSuffix tail
      | _ => .ok (.integer 0))

theorem guardedSuffix_zero (input : Term) :
    guardedSuffix input = .ok (.integer 0) := by
  induction input using guardedSuffix.induct with
  | case1 input ih =>
    unfold guardedSuffix
    split at ih <;> simp_all [Erlang.erlang.«is_integer/1»]
    split <;> rfl

-- Guard preprocessing retains the accepted comparison, and every pure bind
-- retains its equation for well-founded recursion on computed results.
private def halve (input : Term) : Except Exception Term :=
  Except.guard (Erlang.erlang.«>/2» input (.integer 1))
    (fun _ => do
      let smaller ← Erlang.erlang.«-/2» input (.integer 1)
      let half ← Erlang.erlang.«div/2» smaller (.integer 2)
      halve half)
    (fun _ => .ok input)
termination_by match input with | .integer n => n.toNat | _ => 0
decreasing_by
  rename_i passed smallerEq halfEq
  cases smaller <;> simp [Erlang.erlang.«div/2»] at halfEq
  rename_i sm
  subst half
  have shape := (Erlang.erlang.«-/2_integer_result» input 1 sm).mp smallerEq
  subst input
  simp [Except.guardPassed, Erlang.erlang.«>/2»,
    Ordering.isGT_iff_eq_gt, Int.compare_eq_gt] at passed
  have positive : 0 < sm := by
    by_cases h : 1 < sm+1
    · omega
    · simp [h] at passed
  simp [Int.tdiv_eq_ediv_of_nonneg (Int.le_of_lt positive)]
  omega

theorem guard_retains_environment (value : Term) (env : Environment) :
    (Result.guard (.get fun _ => .ok Term.true)
      (fun _ => .ok value) (fun _ => .error (.error (.atom "unexpected")))).run env =
        (.ok value, env) := by
  simp [Result.tryWith, Result.bind, Result.handle]

-- A partial fixed point shaped like OTP's array:find_bits/2: its first
-- parameter is fixed. `partial_fixpoint` proves monotonicity itself.
private def «find/2» (_0 : Term) (_1 : Term) : Except Exception Term := do
  let _2 ← Erlang.erlang.«</2» _0 _1
  match _2 with
  | .atom "true" => pure _1
  | _ => do
    let _3 ← Erlang.erlang.«+/2» _1 (.integer 4)
    «find/2» _0 _3
partial_fixpoint

theorem find_returns : «find/2» (.integer 6) (.integer 0) = .ok (.integer 8) := by
  repeat (rw [«find/2».eq_1]; simp)

-- Recursive calls may appear under handlers, guards, and short-circuit operators.
private def «walk/1» (_0 : Term) : Except Exception Term :=
  Except.guard (Erlang.erlang.«is_integer/1» _0)
    (fun _ => Except.tryWith («walk/1» _0)
      (fun value => Except.andAlso (Except.orElse («walk/1» value) («walk/1» value))
        («walk/1» value))
      (fun _ => «walk/1» _0))
    (fun _ => .ok _0)
partial_fixpoint

/-- A diverging partial fixed point does not return. -/
theorem walk_diverges (n : Int) : «walk/1» (.integer n) = .error .exhausted := by
  refine «walk/1».fixpoint_induct
    (fun walk => ∀ n, walk (.integer n) = .error .exhausted) ?_ ?_ n
  · apply Lean.Order.admissible_pi
    intro n
    exact Lean.Order.admissible_apply
      (fun (_ : Term) (computation : Except Exception Term) => computation = .error .exhausted)
      (.integer n) (Except.admissible_of_bottom _ rfl)
  · intro walk diverges n
    simp [Erlang.erlang.«is_integer/1», diverges]

theorem walk_returns : «walk/1» .nil = .ok .nil := by
  rw [«walk/1»]; rfl

-- A cutoff does not return, and no handler catches it.
private def «cutoff/1» (_0 : Term) : Except Exception Term := Except.cutoff

private def «succeeds/1» (_0 : Term) : Except Exception Term :=
  Except.tryWith («cutoff/1» _0) (fun value => .ok value) (fun _ => pure (Term.atom "caught"))

theorem cutoff_is_not_caught (a : Term) : «succeeds/1» a = .error .exhausted := by
  simp [«succeeds/1», «cutoff/1»]

theorem exhausted_guard_does_not_fall_through :
    Except.guard (.error .exhausted) (fun _ => .ok Term.true) (fun _ => .ok Term.false) =
      .error .exhausted := rfl

theorem exhausted_result_is_not_caught (next : Term → Result) (handler : Exception → Result) :
    Result.tryWith (.error .exhausted) next handler = .error .exhausted ∧
    Result.handle (.error .exhausted) handler = .error .exhausted ∧
    Result.guard (.error .exhausted) (fun _ => .ok Term.true) (fun _ => .ok Term.false) =
      .error .exhausted := ⟨rfl, rfl, rfl⟩

-- Embedded in a process, a computation that does not return ends the run.
theorem exhausted_run (a : Term) :
    Lynx.run (Result.ofExcept («succeeds/1» a)) = .error .exhausted := by
  simp [cutoff_is_not_caught]

end LynxTest.Purity

run_cmd LynxTest.ProofAudit.checkModule `LynxTest.Purity
