module

public import Lynx.Term.DataTypes

public section

namespace Lynx.Dispatcher

open Term

/-- Calling a value that is not a function, or that names no table entry. -/
@[expose] def badfun (function : Term) : Exception :=
  .error (.tuple #[.atom "badfun", function])

/-- Build an Erlang argument list only when reporting an arity mismatch. -/
@[expose] def badarity (function : Term) (arguments : Array Term) : Exception :=
  .error (.tuple #[.atom "badarity", .tuple #[function, arguments.toList.foldr Term.cons Term.nil]])

/-- The entry of the function named `Module:Name/Arity`. -/
@[expose] def find (table : FunTable) (module name : String) (arity : Nat) : Option FunEntry :=
  (table.find? fun def_ => def_.module == module && def_.name == name && def_.arity == arity).map
    (·.entry)

/-- The table entry a function value names and its captured values, once its
arity matches the arguments. -/
@[expose] def lookup (table : FunTable) (function : Term) (arguments : Array Term) :
    Except Exception (FunEntry × Array Term) :=
  match function with
  | .function module name arity captures =>
    if arguments.size = arity then
      match find table module name arity with
      | some entry => .ok (entry, captures)
      | none => .error (badfun function)
    else .error (badarity function arguments)
  | _ => .error (badfun function)

/-- The function value named `Module:Name/Arity`, when the program has one. -/
@[expose] def named (table : FunTable) (module name : Term) (arity : Nat) : Option Term :=
  match module, name with
  | .atom module, .atom name =>
    if (find table module name arity).isSome then some (.function module name arity #[]) else none
  | _, _ => none

/-- Dispatch one call. Entries that dispatch further receive `inner`, and do not
return without one. Pure entries consume no call depth. A pure caller reaches
effectful entries only in programs without any, as translation makes the dynamic
calls of other programs effectful, so they do not return there either. -/
@[expose] def step (table : FunTable) (inner : Option Dispatcher) : Dispatcher where
  pure function arguments :=
    match lookup table function arguments with
    | .error exception => .error exception
    | .ok (.pure body, captures) => body captures arguments
    | .ok (.apply body, captures) =>
      match inner with
      | some inner => body inner captures arguments
      | none => .error .exhausted
    | .ok (.effectful _, _) => .error .exhausted
  call function arguments :=
    match lookup table function arguments with
    | .error exception => .error exception
    | .ok (.pure body, captures) => Result.ofExcept (body captures arguments)
    | .ok (.apply body, captures) =>
      match inner with
      | some inner => Result.ofExcept (body inner captures arguments)
      | none => .error .exhausted
    | .ok (.effectful body, captures) =>
      match inner with
      | some inner => body inner captures arguments
      | none => .error .exhausted
  resolve := named table
  inner := inner

/-- Dispatch through an immutable program table. The depth bounds nested calls
through entries that dispatch further, including in spawned children, and
nested receives, which run with `inner`, but not calls to pure entries;
exceeding it does not return. The lemmas below describe how it calls table
entries, and its body is exposed so closed programs can be evaluated. -/
@[expose] def ofTable (table : FunTable) : Nat → Dispatcher
  | 0 => step table none
  | depth + 1 => step table (some (ofTable table depth))

/-- A pure entry runs without consuming call depth. -/
theorem pure_pure {table : FunTable} {depth arity : Nat} {module name : String} {captures arguments : Array Term}
    {body : Array Term → PureFun}
    (entry : find table module name arity = some (.pure body))
    (size : arguments.size = arity) :
    (ofTable table depth).pure (.function module name arity captures) arguments = body captures arguments := by
  cases depth <;> simp [ofTable, step, lookup, entry, size]

theorem call_pure {table : FunTable} {depth arity : Nat} {module name : String} {captures arguments : Array Term}
    {body : Array Term → PureFun}
    (entry : find table module name arity = some (.pure body))
    (size : arguments.size = arity) :
    (ofTable table depth).call (.function module name arity captures) arguments =
      Result.ofExcept (body captures arguments) := by
  cases depth <;> simp [ofTable, step, lookup, entry, size]

/-- An entry that dispatches further consumes one level of call depth. -/
theorem pure_apply {table : FunTable} {depth arity : Nat} {module name : String} {captures arguments : Array Term}
    {body : Dispatcher → Array Term → PureFun}
    (entry : find table module name arity = some (.apply body))
    (size : arguments.size = arity) :
    (ofTable table (depth + 1)).pure (.function module name arity captures) arguments =
      body (ofTable table depth) captures arguments := by
  simp [ofTable, step, lookup, entry, size]

theorem call_apply {table : FunTable} {depth arity : Nat} {module name : String} {captures arguments : Array Term}
    {body : Dispatcher → Array Term → PureFun}
    (entry : find table module name arity = some (.apply body))
    (size : arguments.size = arity) :
    (ofTable table (depth + 1)).call (.function module name arity captures) arguments =
      Result.ofExcept (body (ofTable table depth) captures arguments) := by
  simp [ofTable, step, lookup, entry, size]

theorem call_effectful {table : FunTable} {depth arity : Nat} {module name : String} {captures arguments : Array Term}
    {body : Dispatcher → Array Term → Fun}
    (entry : find table module name arity = some (.effectful body))
    (size : arguments.size = arity) :
    (ofTable table (depth + 1)).call (.function module name arity captures) arguments =
      body (ofTable table depth) captures arguments := by
  simp [ofTable, step, lookup, entry, size]

/-- Entries that dispatch further do not return once the call depth is exhausted. -/
theorem pure_apply_zero {table : FunTable} {arity : Nat} {module name : String} {captures arguments : Array Term}
    {body : Dispatcher → Array Term → PureFun}
    (entry : find table module name arity = some (.apply body))
    (size : arguments.size = arity) :
    (ofTable table 0).pure (.function module name arity captures) arguments = .error .exhausted := by
  simp [ofTable, step, lookup, entry, size]

end Lynx.Dispatcher

namespace Lynx

/-- Monads whose computations call function values through a dispatcher: `Except`
for code that is pure apart from such calls, and `Result` for other code. -/
class Dispatch (m : Type → Type u) where
  dispatch : Dispatcher → Term → Array Term → m Term

instance : Dispatch (Except Exception) := ⟨Dispatcher.pure⟩
instance : Dispatch @Result := ⟨Dispatcher.call⟩

@[simp] theorem dispatch_except (dispatcher : Dispatcher) (function : Term)
    (arguments : Array Term) :
    (Dispatch.dispatch dispatcher function arguments : Except Exception Term) =
      dispatcher.pure function arguments := rfl

@[simp] theorem dispatch_result (dispatcher : Dispatcher) (function : Term)
    (arguments : Array Term) :
    (Dispatch.dispatch dispatcher function arguments : Result) =
      dispatcher.call function arguments := rfl

end Lynx
