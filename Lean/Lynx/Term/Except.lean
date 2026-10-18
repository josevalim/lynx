module

public import Lynx.Term.DataTypes

/-! Pure computations return a value or raise an exception, and make no
runtime requests. Pure functions return `Except Exception`, which makes their
purity hold by construction. Other computations embed their calls with
`Result.ofExcept`. A pure computation may also not return, raising
`Exception.exhausted`, which handlers propagate without catching. -/

public section

namespace Lynx.Except

-- Not a `defeq` theorem: as a `dsimp` step over long translated bodies, the
-- kernel must recheck the whole unfolded body against the original at once.
@[simp] theorem ok_bind (value : α) (next : α → Except Exception β) :
    (Except.ok value >>= next) = next value := id rfl

@[simp] theorem throw_eq_error (exception : Exception) :
    (throw exception : Except Exception α) = .error exception := rfl

@[simp] theorem pure_eq_ok (value : α) : (pure value : Except Exception α) = .ok value := rfl

@[simp] theorem error_bind (exception : Exception) (next : α → Except Exception β) :
    (Except.error exception >>= next) = Except.error exception := rfl

/-- A sequence returns exactly when both steps return. -/
theorem bind_eq_ok (computation : Except Exception α) (next : α → Except Exception β) (value : β) :
    (computation >>= next) = .ok value ↔
      ∃ input, computation = .ok input ∧ next input = .ok value := by
  cases computation <;> simp

/-- Catch only the protected computation. Exceptions raised by either
continuation propagate to an enclosing handler. `exhausted` is not an Erlang
exception, so it propagates without reaching the handler. -/
@[expose] def tryWith (computation : Except Exception α) (next : α → Except Exception β)
    (handler : Exception → Except Exception β) : Except Exception β :=
  match computation with
  | .ok value => next value
  | .error .exhausted => .error .exhausted
  | .error exception => handler exception

@[simp] theorem tryWith_ok (value : α) (next : α → Except Exception β)
    (handler : Exception → Except Exception β) :
    tryWith (.ok value) next handler = next value := rfl

@[simp] theorem tryWith_error (exception : Exception) (next : α → Except Exception β)
    (handler : Exception → Except Exception β) (raised : exception ≠ .exhausted) :
    tryWith (.error exception) next handler = handler exception := by
  cases exception <;> first | rfl | contradiction

@[simp] theorem tryWith_exhausted (next : α → Except Exception β)
    (handler : Exception → Except Exception β) :
    tryWith (.error .exhausted) next handler = .error .exhausted := rfl

/-- Whether a computation did not return. -/
@[expose] def isExhausted : Except Exception α → Bool
  | .error .exhausted => true
  | _ => false

private def cutoffImpl : Except Exception α :=
  panic! "Lynx: reached a translation cutoff"

/-- A translation cutoff does not return. Compiled code panics instead, to
report reaching untranslated code. -/
@[expose, implemented_by cutoffImpl] def cutoff : Except Exception α := .error .exhausted

@[simp] theorem cutoff_eq : (cutoff : Except Exception α) = .error .exhausted := rfl

/-- Erlang `orelse`. The right operand is selected only after the left one
returns `false`; other values raise `badarg`. -/
@[expose, macro_inline] def orElse (left right : Except Exception Term) : Except Exception Term :=
  left >>= fun value => match value with
    | .atom "true" => .ok (.atom "true")
    | .atom "false" => right
    | other => .error (.error (.tuple #[.atom "badarg", other]))

/-- Erlang `andalso`. The right operand is selected only after the left one
returns `true`; other values raise `badarg`. -/
@[expose, macro_inline] def andAlso (left right : Except Exception Term) : Except Exception Term :=
  left >>= fun value => match value with
    | .atom "true" => right
    | .atom "false" => .ok (.atom "false")
    | other => .error (.error (.tuple #[.atom "badarg", other]))

/-- Proofs see the case on the left operand that Core's lowering produces. -/
@[simp] theorem orElse_eq (left right : Except Exception Term) :
    orElse left right = left >>= fun value => match value with
      | .atom "true" => .ok (.atom "true")
      | .atom "false" => right
      | other => .error (.error (.tuple #[.atom "badarg", other])) := rfl

/-- Proofs see the case on the left operand that Core's lowering produces. -/
@[simp] theorem andAlso_eq (left right : Except Exception Term) :
    andAlso left right = left >>= fun value => match value with
      | .atom "true" => right
      | .atom "false" => .ok (.atom "false")
      | other => .error (.error (.tuple #[.atom "badarg", other])) := rfl

/-- Erlang guards select their body only on the atom `true`. -/
@[expose] def guardPassed : Except Exception Term → Bool
  | .ok (.atom value) => value == "true"
  | _ => false

/-- Run a Core guard, falling through on exceptions and values other than `true`. -/
@[expose] def guard (computation : Except Exception Term)
    (body next : Unit → Except Exception α) : Except Exception α :=
  tryWith computation
    (fun value => match value with | .atom "true" => body () | _ => next ())
    (fun _ => next ())

@[simp] theorem guard_eq (computation : Except Exception Term)
    (body next : Unit → Except Exception α) :
    guard computation body next = tryWith computation
      (fun value => match value with | .atom "true" => body () | _ => next ())
      (fun _ => next ()) := rfl

-- Termination proofs see which branch a guard selected.
@[wf_preprocess] theorem guard_wf (computation : Except Exception Term)
    (body next : Unit → Except Exception α) :
    guard computation body next =
      if isExhausted computation then .error .exhausted
      else if guardPassed computation then body () else next () := by
  cases computation with
  | error exception => cases exception <;> rfl
  | ok value =>
    cases value <;> simp [guardPassed, isExhausted]
    rename_i value
    by_cases accepted : value = "true" <;> simp_all

/-- A bind whose continuation also receives the computation's equation. -/
@[expose] def bindWith (computation : Except Exception α)
    (next : (value : α) → computation = .ok value → Except Exception β) : Except Exception β :=
  match (generalizing := false) returned : computation with
  | .ok value => next value returned
  | .error exception => .error exception

-- Termination proofs over values computed by pure calls need their equations.
@[wf_preprocess] theorem bind_wf (computation : Except Exception α)
    (next : α → Except Exception β) :
    computation >>= next =
      bindWith computation (fun value _ => binderNameHint value next (next (wfParam value))) := by
  cases computation <;> rfl

end Lynx.Except

namespace Lynx.Result

@[simp] theorem ofExcept_ok (value : α) : ofExcept (.ok value) = (.ok value : Result α) := rfl

@[simp] theorem ofExcept_error (exception : Exception) :
    ofExcept (.error exception) = (.error exception : Result α) := rfl

/-- Embedded pure calls make no runtime requests. Preprocessing of well-founded
recursion uses this to retain the equations of their binds. -/
@[simp, wf_preprocess] theorem isPure_ofExcept (reply : Except Exception α) :
    IsPure (ofExcept reply) := by
  cases reply <;> trivial

@[simp] theorem ofExcept_eq_ok (reply : Except Exception α) (value : α) :
    ofExcept reply = .ok value ↔ reply = .ok value := by
  cases reply <;> simp [ofExcept]

@[simp] theorem ofExcept_eq_error (reply : Except Exception α) (exception : Exception) :
    ofExcept reply = .error exception ↔ reply = .error exception := by
  cases reply <;> simp [ofExcept]

/-- A bind of an embedded pure call whose continuation also receives the call's
equation, stated about the pure call itself. -/
@[expose] def ofExceptWith (reply : Except Exception α)
    (next : (value : α) → reply = .ok value → Result β) : Result β :=
  match (generalizing := false) returned : reply with
  | .ok value => next value returned
  | .error exception => .error exception

-- Termination proofs over values computed by embedded pure calls see the
-- equations of those calls, like pure functions do.
@[wf_preprocess ↓] theorem ofExcept_bind_wf (reply : Except Exception α) (next : α → Result β) :
    ofExcept reply >>= next =
      ofExceptWith reply (fun value _ => binderNameHint value next (next (wfParam value))) := by
  cases reply <;> rfl

@[wf_preprocess ↓] theorem ofExcept_bind_explicit_wf (reply : Except Exception α)
    (next : α → Result β) :
    Result.bind (ofExcept reply) next =
      ofExceptWith reply (fun value _ => binderNameHint value next (next (wfParam value))) := by
  cases reply <;> rfl

end Lynx.Result
